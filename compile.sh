#!/bin/bash
#!/bin/bash -e
#!/usr/bin/env bash

FILENAME=${1?Error: no file name given}
echo $FILENAME

ASMEXTENSSION=".asm"
OBJEXTENSSION=".obj"
EXEEXTENSSION=".exe"

python UpdatedCompiler.py

./nasm.exe -f win32 $FILENAME$ASMEXTENSSION

./link.exe /OUT:$FILENAME$EXEEXTENSSION msvcrtd.lib $FILENAME$OBJEXTENSSION

./$FILENAME$EXEEXTENSSION