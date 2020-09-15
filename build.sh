set -x
gcc tools/drat-trim.c    -O2 -o tools/drat-trim
gcc tools/color-encode.c -O2 -o tools/color-encode
cd march_cu
make
