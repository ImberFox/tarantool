#ifndef TARANTOOL_CONFIG_H_INCLUDED
#define TARANTOOL_CONFIG_H_INCLUDED
/*
 * This file is generated by CMake. The original file is called
 * config.h.cmake. Please do not modify.
 */
/*
 * A string with major-minor-patch-commit-id identifier of the
 * release.
 */
#define TARANTOOL_VERSION "@TARANTOOL_VERSION@"
/*  Defined if building for Linux */
#cmakedefine TARGET_OS_LINUX 1
/*  Defined if building for FreeBSD */
#cmakedefine TARGET_OS_FREEBSD 1
/*
 * Defined if gcov instrumentation should be enabled.
 */
#cmakedefine ENABLE_GCOV 1
/*
 * Defined if configured with ENABLE_TRACE (debug trace into
 * a file specified by TRANTOOL_TRACE environment variable.
 */
#cmakedefine ENABLE_TRACE 1
/*
 * Defined if configured with ENABLE_BACKTRACE ('show fiber'
 * showing fiber call stack.
 */
#cmakedefine ENABLE_BACKTRACE 1
/*
 * Set if the system has bfd.h header and GNU bfd library.
 */
#cmakedefine HAVE_BFD 1
#cmakedefine HAVE_MAP_ANON 1
#cmakedefine HAVE_MAP_ANONYMOUS 1
#if !defined(HAVE_MAP_ANONYMOUS) && defined(HAVE_MAP_ANON)
/*
 * MAP_ANON is deprecated, MAP_ANONYMOUS should be used instead.
 * Unfortunately, it's not universally present (e.g. not present
 * on FreeBSD.
 */
#define MAP_ANONYMOUS MAP_ANON
#endif

/*
 * Set if this is a GNU system and libc has __libc_stack_end.
 */
#cmakedefine HAVE_LIBC_STACK_END 1
/*
 * Defined if this is a big-endian system.
 */
#cmakedefine HAVE_BYTE_ORDER_BIG_ENDIAN 1
/*
 * predefined /etc directory prefix.
 */
#define SYSCONF_DIR "@CMAKE_SYSCONF_DIR@"
#define INSTALL_PREFIX "@CMAKE_INSTALL_PREFIX@"
#define BUILD_TYPE "@CMAKE_BUILD_TYPE@"
#define BUILD_INFO "@TARANTOOL_BUILD@"
#define BUILD_CFLAGS "@CMAKE_C_FLAGS@ @core_cflags@"
#define BUILD_OPTIONS "cmake . @TARANTOOL_OPTIONS@"
/*
 * vim: syntax=c
 */
#endif /* TARANTOOL_CONFIG_H_INCLUDED */
