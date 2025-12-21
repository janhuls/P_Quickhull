@echo off

REM This file does essentially the same as 'cabal run quickhull-test',
REM except that it separately calls 'cabal build' and then runs the
REM quickhull-test executable. This _should_ not matter, but for some
REM reason 'cabal' sometimes hangs on Windows at the end of an
REM Accelerate-using program.
REM
REM Usage:
REM  .\build_and_test.cmd                              # run the full test suite
REM  .\build_and_test.cmd --pattern initialPartition   # run just the initialPartition test
REM  .\build_and_test.cmd -p initialPartition          # same as the previous
REM With this script, unlike with cabal, you do not need to use '--'.

setlocal enableextensions EnableDelayedExpansion
cabal build
for /f "delims=" %%a in ('cabal list-bin quickhull-test') do (
  set executable=%%a
)
!executable! %*
