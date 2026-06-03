@echo off
setlocal EnableExtensions

set "LOCAL=C:\Users\saito\Git\ghidra-docker-env"
set "REMOTE=\\100.118.152.92\ubuntu-share"
set "REDUCED_DIR=logs\equivalence_all\function_call_test_phase2_gate_reduced_pre_producer"

if not exist "%LOCAL%\" (
  echo Error: local repo path not found: %LOCAL%
  exit /b 1
)

if not exist "%REMOTE%\" (
  echo Error: remote share path not found: %REMOTE%
  exit /b 1
)

call :copy_files "%REMOTE%" "%LOCAL%" "*gate_reduced*stdout*.log"
if errorlevel 1 exit /b 1

call :copy_files "%REMOTE%" "%LOCAL%" "*phase2*gate*reduced*.log"
if errorlevel 1 exit /b 1

call :copy_tree "%REMOTE%\%REDUCED_DIR%" "%LOCAL%\%REDUCED_DIR%"
if errorlevel 1 exit /b 1

echo.
echo Phase 2 gate reduced matrix artifact copy finished.
echo   From: %REMOTE%\%REDUCED_DIR%
echo   To  : %LOCAL%\%REDUCED_DIR%
exit /b 0

:copy_files
set "SRC=%~1"
set "DST=%~2"
set "MASK=%~3"
echo.
echo robocopy "%SRC%" "%DST%" "%MASK%" /R:2 /W:2
robocopy "%SRC%" "%DST%" "%MASK%" /R:2 /W:2
set "RC=%ERRORLEVEL%"
if %RC% GEQ 8 (
  echo Error: robocopy failed with exit code %RC% for %MASK%
  exit /b 1
)
exit /b 0

:copy_tree
set "SRC=%~1"
set "DST=%~2"
if not exist "%SRC%\" (
  echo Error: remote gate reduced matrix directory not found: %SRC%
  exit /b 1
)
echo.
echo robocopy "%SRC%" "%DST%" /E /R:2 /W:2
robocopy "%SRC%" "%DST%" /E /R:2 /W:2
set "RC=%ERRORLEVEL%"
if %RC% GEQ 8 (
  echo Error: robocopy failed with exit code %RC% for gate reduced matrix logs
  exit /b 1
)
exit /b 0
