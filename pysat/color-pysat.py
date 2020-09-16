from pysat.solvers import Glucose3
from pysat.card import *
import sys

s = Glucose3()
cnf = CNF()

with open(sys.argv[1]) as f:
    content = f.readlines()

nodes=int(content[0].split()[2])
edges=int(content[0].split()[3])
k=int(sys.argv[2])

variables = []
id = 1
for x in range(1,nodes+1):
  v = []
  for color in range(0, k):
    v.append(id)
    id = id + 1
  # each node can be assigned a value between 1 and k  
  amo = CardEnc.atmost(v, encoding=EncType.pairwise)
  for c in amo.clauses: # amo
     cnf.append(c)
  cnf.append(v) # alo
  variables.append(v)

for line in content:
  if line[0]=='p':
  	continue
  else:
    edge=line.split()
    # if two nodes are connected then they have different colors
    for color in range(0, k):
      cnf.append([-variables[int(edge[1])-1][color],-variables[int(edge[2])-1][color]])

s.append_formula(cnf.clauses)
cnf.to_file('color.cnf')
print(s.solve())
print(s.get_model())
# decoding the model
if len(s.get_model()) > 0:
  for x in range(0,nodes):
    for color in range(0, k):
      if s.get_model()[variables[x][color]-1] > 0:
        print("node=",x+1,"is assigned color=",color+1)
