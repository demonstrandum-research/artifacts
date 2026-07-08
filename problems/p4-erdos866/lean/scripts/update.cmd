@echo off
rem Launched at IDLE priority (start /LOW); children inherit the class.
cd /d C:\Users\jacks\source\repos\maths\problems\p4-erdos866\lean
set PATH=%USERPROFILE%\.elan\bin;%PATH%
lake update > scripts\update.log 2>&1
echo EXITCODE %ERRORLEVEL% >> scripts\update.log
