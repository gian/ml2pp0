#!/bin/sh

for f in *.sml
do
	echo "[Test: $f]"
	../bin/mlc $f > result_$f.out
done
