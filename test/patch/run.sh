#!/bin/sh

DIR=$(dirname "$0")

SYS4C="${SYS4C:-sys4c}"
AIN_FILE="${AIN_FILE:-$(mktemp --suffix=.ain)}"
BASE_AIN_FILE="${AIN_FILE%.ain}-base.ain"

if ! "$SYS4C" compile -o "$BASE_AIN_FILE" "$DIR/main.jaf"; then
    echo compile failed
    rm -f "$BASE_AIN_FILE"
    exit 1
fi

if ! "$SYS4C" patch --base-ain="$BASE_AIN_FILE" --source="$DIR/fixes.jaf" \
        -o "$AIN_FILE" "$DIR/patch.pje"; then
    echo patch failed
    rm -f "$BASE_AIN_FILE" "$AIN_FILE"
    exit 1
fi
rm -f "$BASE_AIN_FILE"

if ! ${XSYSTEM4:-xsystem4} --nodebug --save-folder=. "$AIN_FILE"; then
    echo execution failed
    rm -f "$AIN_FILE"
    exit 1
fi

echo passed
rm -f "$AIN_FILE"
