CNF=$1
~/ubcsat/ubcsat -alg ddfw -i $CNF -cutoff 10000000 -runs 10
