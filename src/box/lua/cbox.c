/*
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * Copyright 2010-2020, Tarantool AUTHORS, please see AUTHORS file.
 */

#include <string.h>
#include <lua.h>

#include "tt_static.h"
#include "assoc.h"
#include "diag.h"
#include "port.h"
#include "say.h"

#include "box/error.h"
#include "box/func.h"
#include "box/call.h"
#include "box/port.h"

#include "trivia/util.h"
#include "lua/utils.h"

/** Function names to descriptor map. */
static struct mh_strnptr_t *func_hash;

/**
 * Function descriptor.
 */
struct cbox_func {
	/**
	 * Symbol descriptor for the function in
	 * an associated module.
	 */
	struct module_sym mod_sym;

	/** Function name length */
	size_t name_len;

	/** Function name */
	char name[0];
};

/**
 * Find function descriptor by its name.
 */
struct cbox_func *
cbox_func_find(const char *name, size_t len)
{
	if (name != NULL && len > 0) {
		mh_int_t e = mh_strnptr_find_inp(func_hash, name, len);
		if (e != mh_end(func_hash))
			return mh_strnptr_node(func_hash, e)->val;
	}
	return NULL;
}

/**
 * Add function descriptor to the cache.
 */
static int
cbox_func_add(struct cbox_func *cfunc)
{
	const struct mh_strnptr_node_t nd = {
		.str	= cfunc->name,
		.len	= cfunc->name_len,
		.hash	= mh_strn_hash(cfunc->name, cfunc->name_len),
		.val	= cfunc,
	};

	mh_int_t h = mh_strnptr_put(func_hash, &nd, NULL, NULL);
	if (h == mh_end(func_hash)) {
		diag_set(OutOfMemory, sizeof(nd), __func__, "h");
		return -1;
	}
	return 0;
}

/**
 * Setup a detailed error description into the diagnostics area.
 */
static void
diag_set_param_error(struct lua_State *L, int idx, const char *func_name,
		     const char *param, const char *exp)
{
	const char *typename = idx == 0 ?
		"<unknown>" : lua_typename(L, lua_type(L, idx));
	static const char *fmt =
		"%s: wrong parameter \"%s\": expected %s, got %s";
	diag_set(IllegalParams, fmt, func_name, param, exp, typename);
}

/**
 * Call function by its name from the Lua code.
 */
static int
lcbox_func_call(struct lua_State *L)
{
	int nr_args = lua_gettop(L);

	/*
	 * A function name is associated with the variable.
	 */
	lua_getfield(L, -nr_args, "name");
	size_t name_len;
	const char *name = lua_tolstring(L, -1, &name_len);
	struct cbox_func *cf = cbox_func_find(name, name_len);
	/*
	 * Do not pop the result early, since Lua's GC may
	 * drop the name string found.
	 */
	lua_pop(L, 1);

	if (cf == NULL) {
		/*
		 * This can happen if someone changed the
		 * name of the function manually.
		 */
		const char *fmt = tnt_errcode_desc(ER_FUNCTION_EXISTS);
		diag_set(IllegalParams, fmt, name);
		return luaT_push_nil_and_error(L);
	}

	/*
	 * FIXME: We should get rid of luaT_newthread but this
	 * requires serious modifucations. In particular
	 * port_lua_do_dump uses tarantool_L reference and
	 * coro_ref must be valid as well.
	 */
	lua_State *args_L = luaT_newthread(tarantool_L);
	if (args_L == NULL)
		return luaT_push_nil_and_error(L);

	int coro_ref = luaL_ref(tarantool_L, LUA_REGISTRYINDEX);
	lua_xmove(L, args_L, lua_gettop(L) - 1);

	struct port args;
	port_lua_create(&args, args_L);
	((struct port_lua *)&args)->ref = coro_ref;

	struct port ret;
	if (module_sym_call(&cf->mod_sym, &args, &ret) != 0) {
		port_destroy(&args);
		return luaT_push_nil_and_error(L);
	}

	int top = lua_gettop(L);
	lua_pushboolean(L, true);
	port_dump_lua(&ret, L, true);
	int cnt = lua_gettop(L) - top;

	port_destroy(&ret);
	port_destroy(&args);

	return cnt;
}

/**
 * Create a new function.
 *
 * This function takes a function name from the caller
 * stack @a L and creates a new function object.
 *
 * Possible errors:
 *
 * - IllegalParams: function name is either not supplied
 *   or not a string.
 * - IllegalParams: a function is already created.
 * - OutOfMemory: unable to allocate a function.
 *
 * @returns function object on success or {nil,error} on error,
 * the error is set to the diagnostics area.
 */
static int
lcbox_func_create(struct lua_State *L)
{
	const char *method = "cbox.func.create";
	struct cbox_func *cf = NULL;

	if (lua_gettop(L) != 1) {
		const char *fmt = "Expects %s(\'name\')";
		diag_set(IllegalParams, fmt, method);
		goto out;
	}

	if (lua_type(L, 1) != LUA_TSTRING) {
		diag_set_param_error(L, 1, method,
				     lua_tostring(L, 1),
				     "function name");
		goto out;
	}

	size_t name_len;
	const char *name = lua_tolstring(L, 1, &name_len);

	if (cbox_func_find(name, name_len) != NULL) {
		const char *fmt = tnt_errcode_desc(ER_FUNCTION_EXISTS);
		diag_set(IllegalParams, fmt, name);
		goto out;
	}

	size_t size = sizeof(*cf) + name_len + 1;
	cf = malloc(size);
	if (cf == NULL) {
		diag_set(OutOfMemory, size, "malloc", "cf");
		goto out;
	}

	cf->mod_sym.addr	= NULL;
	cf->mod_sym.module	= NULL;
	cf->mod_sym.name	= cf->name;
	cf->name_len		= name_len;

	memcpy(cf->name, name, name_len);
	cf->name[name_len] = '\0';

	if (cbox_func_add(cf) != 0)
		goto out;

	/*
	 * A new variable should be callable for
	 * convenient use in Lua.
	 */
	lua_newtable(L);

	lua_pushstring(L, "name");
	lua_pushstring(L, cf->name);
	lua_settable(L, -3);

	lua_newtable(L);

	lua_pushstring(L, "__call");
	lua_pushcfunction(L, lcbox_func_call);
	lua_settable(L, -3);

	lua_setmetatable(L, -2);
	return 1;

out:
	free(cf);
	return luaT_push_nil_and_error(L);
}

/**
 * Drop a function.
 *
 * This function takes a function name from the caller
 * stack @a L and drops a function object.
 *
 * Possible errors:
 *
 * - IllegalParams: function name is either not supplied
 *   or not a string.
 * - IllegalParams: the function does not exist.
 *
 * @returns true on success or {nil,error} on error,
 * the error is set to the diagnostics area.
 */
static int
lcbox_func_drop(struct lua_State *L)
{
	const char *method = "cbox.func.drop";
	const char *name = NULL;

	if (lua_gettop(L) != 1) {
		const char *fmt = "expects %s(\'name\')";
		diag_set(IllegalParams, fmt, method);
		return luaT_push_nil_and_error(L);
	}

	if (lua_type(L, 1) != LUA_TSTRING) {
		diag_set_param_error(L, 1, method,
				     lua_tostring(L, 1),
				     "function name or id");
		return luaT_push_nil_and_error(L);
	}

	size_t name_len;
	name = lua_tolstring(L, 1, &name_len);

	mh_int_t e = mh_strnptr_find_inp(func_hash, name, name_len);
	if (e == mh_end(func_hash)) {
		const char *fmt = tnt_errcode_desc(ER_NO_SUCH_FUNCTION);
		diag_set(IllegalParams, fmt, name);
		return luaT_push_nil_and_error(L);
	}

	struct cbox_func *cf = mh_strnptr_node(func_hash, e)->val;
	mh_strnptr_del(func_hash, e, NULL);
	free(cf);

	lua_pushboolean(L, true);
	return 1;
}

/**
 * Reload a module.
 *
 * This function takes a module name from the caller
 * stack @a L and reloads all functions associated with
 * the module.
 *
 * Possible errors:
 *
 * - IllegalParams: module name is either not supplied
 *   or not a string.
 * - IllegalParams: the function does not exist.
 * - ClientError: a module with the name provided does
 *   not exist.
 *
 * @returns true on success or {nil,error} on error,
 * the error is set to the diagnostics area.
 */
static int
lcbox_module_reload(struct lua_State *L)
{
	const char *method = "cbox.module.reload";
	const char *fmt = "Expects %s(\'name\') but no name passed";

	if (lua_gettop(L) != 1 || !lua_isstring(L, 1)) {
		diag_set(IllegalParams, fmt, method);
		return luaT_push_nil_and_error(L);
	}

	size_t name_len;
	const char *name = lua_tolstring(L, 1, &name_len);
	if (name == NULL || name_len < 1) {
		diag_set(IllegalParams, fmt, method);
		return luaT_push_nil_and_error(L);
	}

	struct module *module = NULL;
	if (module_reload(name, &name[name_len], &module) == 0) {
		if (module != NULL) {
			lua_pushboolean(L, true);
			return 1;
		}
		diag_set(ClientError, ER_NO_SUCH_MODULE, name);
	}
	return luaT_push_nil_and_error(L);
}

/**
 * Initialize cbox Lua module.
 *
 * @param L Lua state where to register the cbox module.
 */
void
box_lua_cbox_init(struct lua_State *L)
{
	static const struct luaL_Reg cbox_methods[] = {
		{ NULL, NULL }
	};
	luaL_register_module(L, "cbox", cbox_methods);

	/* func table */
	static const struct luaL_Reg func_table[] = {
		{ "create",	lcbox_func_create },
		{ "drop",	lcbox_func_drop },
	};

	lua_newtable(L);
	for (size_t i = 0; i < lengthof(func_table); i++) {
		lua_pushstring(L, func_table[i].name);
		lua_pushcfunction(L, func_table[i].func);
		lua_settable(L, -3);
	}
	lua_setfield(L, -2, "func");

	/* module table */
	static const struct luaL_Reg module_table[] = {
		{ "reload",	lcbox_module_reload },
	};

	lua_newtable(L);
	for (size_t i = 0; i < lengthof(module_table); i++) {
		lua_pushstring(L, module_table[i].name);
		lua_pushcfunction(L, module_table[i].func);
		lua_settable(L, -3);
	}
	lua_setfield(L, -2, "module");

	lua_pop(L, 1);
}

/**
 * Initialize cbox module.
 *
 * @return 0 on success, -1 on error (diag is set).	
 */
int
cbox_init(void)
{
	func_hash = mh_strnptr_new();
	if (func_hash == NULL) {
		diag_set(OutOfMemory, sizeof(*func_hash), "malloc",
			  "cbox.func hash table");
		return -1;
	}
	return 0;
}

/**
 * Free cbox module.
 */
void
cbox_free(void)
{
	while (mh_size(func_hash) > 0) {
		mh_int_t e = mh_first(func_hash);
		struct cbox_func *cf = mh_strnptr_node(func_hash, e)->val;
		module_sym_unload(&cf->mod_sym);
		mh_strnptr_del(func_hash, e, NULL);
	}
	mh_strnptr_delete(func_hash);
	func_hash = NULL;
}
