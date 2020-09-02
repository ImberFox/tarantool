/*
 * Copyright 2010-2017, Tarantool AUTHORS, please see AUTHORS file.
 *
 * Redistribution and use in source and binary forms, with or
 * without modification, are permitted provided that the following
 * conditions are met:
 *
 * 1. Redistributions of source code must retain the above
 *    copyright notice, this list of conditions and the
 *    following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above
 *    copyright notice, this list of conditions and the following
 *    disclaimer in the documentation and/or other materials
 *    provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY <COPYRIGHT HOLDER> ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL
 * <COPYRIGHT HOLDER> OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
 * BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

/*
 * Internal interface definitions for datetime support in sql.
 *
 */

#ifndef dateINT_H
#define dateINT_H

#include "sqlInt.h"
#include "vdbeInt.h"

/*
 *    julianday( TIMESTRING, MOD, MOD, ...)
 *
 * Return the julian day number of the date specified in the arguments
 */
void
juliandayFunc(sql_context * context, int argc, sql_value ** argv);

/*
 *    datetime( TIMESTRING, MOD, MOD, ...)
 *
 * Return YYYY-MM-DD HH:MM:SS
 */
void
datetimeFunc(sql_context * context, int argc, sql_value ** argv);

/*
 *    time( TIMESTRING, MOD, MOD, ...)
 *
 * Return HH:MM:SS
 */
void
timeFunc(sql_context * context, int argc, sql_value ** argv);

/*
 *    date( TIMESTRING, MOD, MOD, ...)
 *
 * Return YYYY-MM-DD
 */
void
dateFunc(sql_context * context, int argc, sql_value ** argv);

/*
 *    strftime( FORMAT, TIMESTRING, MOD, MOD, ...)
 *
 * Return a string described by FORMAT.  Conversions as follows:
 *
 *   %d  day of month
 *   %f  * fractional seconds  SS.SSS
 *   %H  hour 00-24
 *   %j  day of year 000-366
 *   %J  * julian day number
 *   %m  month 01-12
 *   %M  minute 00-59
 *   %s  seconds since 1970-01-01
 *   %S  seconds 00-59
 *   %w  day of week 0-6  sunday==0
 *   %W  week of year 00-53
 *   %Y  year 0000-9999
 *   %%  %
 */
void
strftimeFunc(sql_context * context, int argc, sql_value ** argv);

/*
 * current_time()
 *
 * This function returns the same value as time('now').
 */
void
ctimeFunc(sql_context * context, int NotUsed, sql_value ** NotUsed2);

/*
 * current_date()
 *
 * This function returns the same value as date('now').
 */
void
cdateFunc(sql_context * context, int NotUsed, sql_value ** NotUsed2);

/*
 * current_timestamp()
 *
 * This function returns the same value as datetime('now').
 */
void
ctimestampFunc(sql_context * context, int NotUsed, sql_value ** NotUsed2);


#endif				/* dateINT_H */
