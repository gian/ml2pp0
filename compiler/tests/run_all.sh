#!/bin/sh

for f in *.sml
do
	echo "[Test: $f]"
	../bin/ml2pp0 $f > result_$f.out
done
