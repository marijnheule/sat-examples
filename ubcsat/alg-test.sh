CNF=$1
CUTOFF=$2
RUNS=$3

if [ -z "$CUTOFF" ]; then CUTOFF=100000; fi
if [ -z "$RUNS"   ]; then   RUNS=10;     fi

for ALG in `cat algs.txt`
do
  ubcsat -alg $ALG -i $CNF -runs $RUNS -cutoff $CUTOFF
done
