#include <stdio.h>
#include <stdbool.h>
#include <msgpuck.h>

#include "module.h"

/*
 * Just make sure we've been called.
 */
int
cfunc_nop(box_function_ctx_t *ctx, const char *args, const char *args_end)
{
	(void)ctx;
	(void)args;
	(void)args_end;
	return 0;
}

/*
 * Fetch first N even numbers (just to make sure the order of
 * arguments is not screwed).
 */
int
cfunc_fetch_evens(box_function_ctx_t *ctx, const char *args, const char *args_end)
{
	int arg_count = mp_decode_array(&args);
	if (arg_count != 1) {
		return box_error_set(__FILE__, __LINE__, ER_PROC_C, "%s",
			"invalid argument count");
	}
	int field_count = mp_decode_array(&args);
	if (field_count < 1) {
		return box_error_set(__FILE__, __LINE__, ER_PROC_C, "%s",
			"invalid array size");
	}

	for (int i = 0; i < field_count; i++) {
		int val = mp_decode_uint(&args);
		int needed = 2 * (i+1);
		if (val != needed) {
			char res[128];
			snprintf(res, sizeof(res), "%s %d != %d",
				 "invalid argument", val, needed);
			return box_error_set(__FILE__, __LINE__,
					     ER_PROC_C, "%s", res);
		}
	}

	return 0;
}

/*
 * Return one element array twice.
 */
int
cfunc_multireturn(box_function_ctx_t *ctx, const char *args, const char *args_end)
{
	char tuple_buf[512];
	char *d = tuple_buf;
	d = mp_encode_array(d, 1);
	d = mp_encode_uint(d, 1);
	assert(d <= tuple_buf + sizeof(tuple_buf));

	box_tuple_format_t *fmt = box_tuple_format_default();
	box_tuple_t *tuple_a = box_tuple_new(fmt, tuple_buf, d);
	if (tuple_a == NULL)
		return -1;
	int rc = box_return_tuple(ctx, tuple_a);
	if (rc != 0)
		return rc;
	return box_return_tuple(ctx, tuple_a);
}

/*
 * Encode int + string pair back.
 */
int
cfunc_args(box_function_ctx_t *ctx, const char *args, const char *args_end)
{
	uint32_t arg_count = mp_decode_array(&args);
	if (arg_count != 2) {
		return box_error_set(__FILE__, __LINE__, ER_PROC_C, "%s",
			"invalid argument count");
	}

	if (mp_typeof(*args) != MP_UINT) {
		return box_error_set(__FILE__, __LINE__, ER_PROC_C, "%s",
			"tuple field must be uint");
	}
	uint32_t num = mp_decode_uint(&args);

	if (mp_typeof(*args) != MP_STR) {
		return box_error_set(__FILE__, __LINE__, ER_PROC_C, "%s",
			"tuple field must be string");
	}
	const char *str = args;
	uint32_t len = mp_decode_strl(&str);

	char tuple_buf[512];
	char *d = tuple_buf;
	d = mp_encode_array(d, 2);
	d = mp_encode_uint(d, num);
	d = mp_encode_str(d, str, len);
	assert(d <= tuple_buf + sizeof(tuple_buf));

	box_tuple_format_t *fmt = box_tuple_format_default();
	box_tuple_t *tuple = box_tuple_new(fmt, tuple_buf, d);
	if (tuple == NULL)
		return -1;

	return box_return_tuple(ctx, tuple);
}
