@echo off
setlocal EnableExtensions

set "LOCAL=C:\Users\saito\Git\ghidra-docker-env"
set "REMOTE=\\100.118.152.92\ubuntu-share"

if not exist "%LOCAL%\" (
  echo Error: local repo path not found: %LOCAL%
  exit /b 1
)

if not exist "%REMOTE%\" (
  echo Error: remote share path not found: %REMOTE%
  exit /b 1
)

call :copy_files "%REMOTE%" "%LOCAL%" "unit_tests_stdout.log"
if errorlevel 1 exit /b 1

call :copy_files "%REMOTE%" "%LOCAL%" "*_stdout.log"
if errorlevel 1 exit /b 1

call :copy_tree "%REMOTE%\logs\equivalence_all" "%LOCAL%\logs\equivalence_all"
if errorlevel 1 exit /b 1

echo.
echo Artifact copy finished.
echo   From: %REMOTE%
echo   To  : %LOCAL%
echo Note: In the robocopy summary, Extras are not copy failures. With /MIR, Extras are local-only items that are removed from logs\equivalence_all. Only robocopy exit codes 8 or higher are treated as failures here.
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
  echo Error: remote logs directory not found: %SRC%
  exit /b 1
)
echo.
echo robocopy "%SRC%" "%DST%" /MIR /R:2 /W:2
echo Note: /MIR removes local extras under logs\equivalence_all so stale gate JSON files do not remain.
robocopy "%SRC%" "%DST%" /MIR /R:2 /W:2
set "RC=%ERRORLEVEL%"
if %RC% GEQ 8 (
  echo Error: robocopy failed with exit code %RC% for logs/equivalence_all
  exit /b 1
)
exit /b 0
