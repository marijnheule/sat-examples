from z3 import *
import sys

s = Solver()

with open(sys.argv[1]) as f:
    content = f.readlines()

nodes=int(content[0].split()[2])
edges=int(content[0].split()[3])

variables = []
for id in range(1,nodes+1):
	variables.append(Int('x'+str(id)))
	# each node can be assigned a value between 1 and k
	s.add(And(1 <= variables[id-1], variables[id-1] <= int(sys.argv[2])))

for line in content:
  if line[0]=='p':
  	continue
  else:
  	edge=line.split()
  	# if two nodes are connected then they have different colors
  	s.add((variables[int(edge[1])-1])!=(variables[int(edge[2])-1]))

print s # formula
print(s.check()) # sat/unsat
print(s.model()) # model if sat
