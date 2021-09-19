#!/bin/sh
cd ..
./configure && make
install -s build/cadical bin/
