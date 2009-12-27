#!/bin/sh

dot -Grankdir=LR -Earrowsize=0.5 -Tpng < $1.dot > $1.png

