#!/bin/sh -eu

make
./meta-cedille --load TestFiles/Fail --no-repl 2> /dev/null && exit 1
./meta-cedille --load TestFiles/Test --no-repl
