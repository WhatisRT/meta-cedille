#!/bin/bash

# pre-commit.sh
STASH_NAME="pre-commit-$(date +%s)"
git stash save -q --keep-index $STASH_NAME

./run_tests.sh
RESULT=$?

git stash pop -q

[ $RESULT -ne 0 ] && exit 1
exit 0
