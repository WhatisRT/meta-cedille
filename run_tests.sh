#!/bin/sh -eu

make
./meta-cedille --load test/Fail --no-repl 2> /dev/null && exit 1
./meta-cedille --load test/Test --no-repl
