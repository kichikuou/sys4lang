#!/bin/sh

cd $(dirname "$0")

./test-runner.sh main.jaf
./test-runner.sh arith.jaf
./test-runner.sh string.jaf
./test-runner.sh array.jaf
./test-runner.sh struct.jaf
./test-runner.sh class.jaf
./test-runner.sh delegate.jaf
./test-runner.sh control.jaf
./test-runner.sh ref.jaf
./test-runner.sh functype.jaf
./test-runner.sh message.jaf
./test-runner.sh char-constant.jaf
./test-runner.sh override.jaf
./test-runner.sh const.jaf
./test-runner.sh unicode.jaf
