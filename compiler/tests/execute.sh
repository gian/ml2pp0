#!/bin/sh

for f in test*[^sml]
do
	echo "[Executing $f]"
	./$f
done

