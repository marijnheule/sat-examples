Steps to run experiments on StarExec

1. Create a subspace in your area:
+subspaces -> add subspace

Each subspace is like a directory where benchmarks, solvers, and job
outputs are stored

2. Upload a solver to that subspace:
solvers+ -> upload solver

You should upload a tar, tar.gz, tgz, or zip file with a particular
directory structure. More details at:
https://www.starexec.org/starexec/secure/help.jsp?ref=/starexec/secure/add/solver.help

Run the script create_zip.sh to clone the latest version of CaDiCaL
and add the required files for StarExec and zip the result.

The differences wrt the original CaDiCaL:
- starexec_build : StarExec will run this script when you upload your
solver and will compile it

- bin : this directory will contain the binary of your solver and any
scripts to run the solver (I added 4 scripts, 1 for each version we
discussed today). Also, note that those scripts must start with
starexec_run_*

If everything went ok, then you should have your solver in StarExec.

3. Upload benchmarks to the same directory.

benchmarks+ -> upload benchmarks

Since benchmarks often take a lot of space, I usually compress then
(e.g., using bzip2). CaDiCal can take as input compressed files.

4. Create a job.

jobs+ -> create job -> choose worker queue long.q (the all.q only
allows time limit of at most 1800 seconds but you should be able to
set a larger time limit in long.q)

You can do this in the subspace that you just created. This will run
the solvers you select on the benchmarks of that subspace (or a
selected subset of them).

5. Download the job output.

Once the job is done, you can download the job output and check the
logs of CaDiCal to gather the statistics regarding the average and
mean level.

6. Deletion

When you delete something, it will go to the recycle bin. You need to
empty the recycle bin to completely delete it. From the Account ->
Profile you can also see how jobs, solver, and benchmarks in a single
place and can delete them from there.
