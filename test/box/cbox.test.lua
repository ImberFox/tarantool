build_path = os.getenv("BUILDDIR")
package.cpath = build_path..'/test/box/?.so;'..build_path..'/test/box/?.dylib;'..package.cpath

cbox = require('cbox')
fio = require('fio')

ext = (jit.os == "OSX" and "dylib" or "so")

cfunc_path = fio.pathjoin(build_path, "test/box/cfunc.") .. ext
cfunc1_path = fio.pathjoin(build_path, "test/box/cfunc1.") .. ext
cfunc2_path = fio.pathjoin(build_path, "test/box/cfunc2.") .. ext

_ = pcall(fio.unlink(cfunc_path))
fio.symlink(cfunc1_path, cfunc_path)

--
-- They all are sitting in cfunc.so
cfunc_nop = cbox.func.create('cfunc.cfunc_nop')
cfunc_fetch_evens = cbox.func.create('cfunc.cfunc_fetch_evens')
cfunc_multireturn = cbox.func.create('cfunc.cfunc_multireturn')
cfunc_args = cbox.func.create('cfunc.cfunc_args')

--
-- Make sure they all are callable
cfunc_nop()
cfunc_fetch_evens()
cfunc_multireturn()
cfunc_args()

--
-- Clean old function references and reload a new one.
_ = pcall(fio.unlink(cfunc_path))
fio.symlink(cfunc2_path, cfunc_path)

cbox.module.reload('cfunc')

cfunc_nop()
cfunc_multireturn()
cfunc_fetch_evens({2,4,6})
cfunc_fetch_evens({1,2,3})  -- error
cfunc_args(1, "hello")
--
-- Clean it up
cbox.func.drop('cfunc.cfunc_nop')
cbox.func.drop('cfunc.cfunc_fetch_evens')
cbox.func.drop('cfunc.cfunc_multireturn')
cbox.func.drop('cfunc.cfunc_args')

--
-- Cleanup the generated symlink
_ = pcall(fio.unlink(cfunc_path))
