#!/bin/sh

echo "; Generated definitions from lib/decs.ll" > decs.ll

cat basis.c | grep "\/\*@" | sed 's/^\/\*@ \(.*\) \*\//\1/' >> decs.ll