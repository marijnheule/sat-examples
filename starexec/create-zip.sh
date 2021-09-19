git clone https://github.com/arminbiere/cadical
cp starexec_build cadical
mkdir cadical/build
cp build.sh cadical/build
mkdir cadical/bin
cp starexec_run_cadical cadical/bin
cd cadical
zip ../cadical.zip -r *
