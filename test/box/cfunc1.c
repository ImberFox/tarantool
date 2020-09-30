#include <stdio.h>
#include <stdbool.h>
#include <msgpuck.h>

#include "module.h"

/*
 * Before the reload functions are just declared
 * and simply exit with zero.
 *
 * After the module reload we should provide real
 * functionality.
 */

int
cfunc_nop(box_function_ctx_t *ctx, const char *args, const char *args_end)
{
	(void)ctx;
	(void)args;
	(void)args_end;
	return 0;
}

int
cfunc_fetch_evens(box_function_ctx_t *ctx, const char *args, const char *args_end)
{
	(void)ctx;
	(void)args;
	(void)args_end;
	return 0;
}

int
cfunc_multireturn(box_function_ctx_t *ctx, const char *args, const char *args_end)
{
	(void)ctx;
	(void)args;
	(void)args_end;
	return 0;
}

int
cfunc_args(box_function_ctx_t *ctx, const char *args, const char *args_end)
{
	(void)ctx;
	(void)args;
	(void)args_end;
	return 0;
}
