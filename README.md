# sat-examples
Simple examples of using SAT solvers

# build
build the tools using: ./build.sh

# plain solving
run a SAT solver: cadical cnf/eq.atree.braun.8.unsat.cnf

# solving on Windows
SAT4j runs on windows: ./sat4j.sh cnf/eq.atree.braun.8.unsat.cnf

# local search
SLS can be much more efficient: ./ubcsat.sh cnf/bce7824.cnf

# lookahead solvers
lookahead is better on random k-SAT: ./march.sh cnf/random-easy.cnf

# proof logging and validation
proof logging:    kissat    cnf/9dlx_vliw_at_b_iq1.cnf proof
proof validation: drat-trim cnf/9dlx_vliw_at_b_iq1.cnf proof
