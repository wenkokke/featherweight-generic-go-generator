#!/bin/sh
nice -n 10 time stack run -- --max-depth=15 --batch-size=100 2> errors.log
