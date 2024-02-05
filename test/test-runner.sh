#!/bin/sh

TEST_FILE="$1"
AIN_FILE="$(mktemp --suffix=.ain)"

printf "Running test $TEST_FILE... "

if ! ${SYS4C:-sys4c} -o "$AIN_FILE" "$TEST_FILE"; then
    echo compile failed
    rm -f "$AIN_FILE"
    exit 1
fi

if ! ${XSYSTEM4:-xsystem4} --nodebug --save-folder=. "$AIN_FILE"; then
    echo execution failed
    rm -f "$AIN_FILE"
    exit 1
fi

echo passed
rm -f "$AIN_FILE"
