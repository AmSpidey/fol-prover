{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
module Paths_prover (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/home/zly/IMPORTANT/STUDIA materia\322y/2 stopie\324/obowi\261zki/logika/prover/my_prover/prover/.stack-work/install/x86_64-linux-tinfo6/861252c52de55fc2d4f63762c32c9226c7f2388d3d3fd2950d288a8a22b67bf8/8.10.4/bin"
libdir     = "/home/zly/IMPORTANT/STUDIA materia\322y/2 stopie\324/obowi\261zki/logika/prover/my_prover/prover/.stack-work/install/x86_64-linux-tinfo6/861252c52de55fc2d4f63762c32c9226c7f2388d3d3fd2950d288a8a22b67bf8/8.10.4/lib/x86_64-linux-ghc-8.10.4/prover-0.1.0.0-6CeIPJLJdYQGSSmbtKbBM-prover-exe"
dynlibdir  = "/home/zly/IMPORTANT/STUDIA materia\322y/2 stopie\324/obowi\261zki/logika/prover/my_prover/prover/.stack-work/install/x86_64-linux-tinfo6/861252c52de55fc2d4f63762c32c9226c7f2388d3d3fd2950d288a8a22b67bf8/8.10.4/lib/x86_64-linux-ghc-8.10.4"
datadir    = "/home/zly/IMPORTANT/STUDIA materia\322y/2 stopie\324/obowi\261zki/logika/prover/my_prover/prover/.stack-work/install/x86_64-linux-tinfo6/861252c52de55fc2d4f63762c32c9226c7f2388d3d3fd2950d288a8a22b67bf8/8.10.4/share/x86_64-linux-ghc-8.10.4/prover-0.1.0.0"
libexecdir = "/home/zly/IMPORTANT/STUDIA materia\322y/2 stopie\324/obowi\261zki/logika/prover/my_prover/prover/.stack-work/install/x86_64-linux-tinfo6/861252c52de55fc2d4f63762c32c9226c7f2388d3d3fd2950d288a8a22b67bf8/8.10.4/libexec/x86_64-linux-ghc-8.10.4/prover-0.1.0.0"
sysconfdir = "/home/zly/IMPORTANT/STUDIA materia\322y/2 stopie\324/obowi\261zki/logika/prover/my_prover/prover/.stack-work/install/x86_64-linux-tinfo6/861252c52de55fc2d4f63762c32c9226c7f2388d3d3fd2950d288a8a22b67bf8/8.10.4/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "prover_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "prover_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "prover_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "prover_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "prover_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "prover_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
