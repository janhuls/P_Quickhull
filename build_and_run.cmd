@echo off

REM This file does essentially the same as 'cabal run quickhull',
REM except that it separately calls 'cabal build' and then runs the
REM quickhull executable. This _should_ not matter, but for some
REM reason 'cabal' sometimes hangs on Windows at the end of an
REM Accelerate-using program.
REM
REM Usage:
REM  .\build_and_run.cmd                       # run the graphical interface with a small random input
REM  .\build_and_run.cmd --file input\10.dat   # use a rather large input
REM With this script, unlike with cabal, you do not need to use '--'.
REM For more options that you can pass, see the assignment
REM description, or '.\build_and_run.cmd --help'.

setlocal enableextensions EnableDelayedExpansion
cabal build
for /f "delims=" %%a in ('cabal list-bin quickhull') do (
  set executable=%%a
)
!executable! %*
