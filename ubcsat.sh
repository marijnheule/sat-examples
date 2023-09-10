CNF=$1
~/ubcsat/ubcsat -alg ddfw -i $CNF -cutoff 3000000 -runs 100 -solve
