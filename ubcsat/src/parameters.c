/*

      ##  ##  #####    #####   $$$$$   $$$$   $$$$$$    
      ##  ##  ##  ##  ##      $$      $$  $$    $$      
      ##  ##  #####   ##       $$$$   $$$$$$    $$      
      ##  ##  ##  ##  ##          $$  $$  $$    $$      
       ####   #####    #####  $$$$$   $$  $$    $$      
  ======================================================
  SLS SAT Solver from The University of British Columbia
  ======================================================
  ...... Developed & Maintained by Dave Tompkins .......
  ------------------------------------------------------
  ...... consult legal.txt for legal information .......
  ------------------------------------------------------
  .... project website: http://ubcsat.dtompkins.com ....
  ------------------------------------------------------
  source repository: https://github.com/dtompkins/ubcsat
  ------------------------------------------------------
  ..... contact us at ubcsat [@] googlegroups.com ......
  ------------------------------------------------------

*/

#include "ubcsat.h"

#ifdef __cplusplus 
namespace ubcsat {
#endif

void AddParameters() {

  AddParmString(&parmAlg,"-alg","algorithm name","","",&sAlgName,"");
  AddParmString(&parmAlg,"-v","algorithm variant name (if any)","some algorithms have multiple variants and you can use~the -v parameter to specify which variant you wish to use","",&sVarName,"");
  AddParmBool(&parmAlg,"-w","use the weighted variant of the algorithm (if it exists)","weighted algorithms solve weighted instances with static~clause weights (weights are specified in .wcnf files)","",&bWeighted,0);

  AddParmBool(&parmHelp,"-help,--help,-h","general help","","",&bShowHelp,0);
  AddParmBool(&parmHelp,"-helpparam,-hp","list ubcsat parameters","","",&bShowHelpP,0);
  AddParmBool(&parmHelp,"-helpalg,-ha","list of available (unweighted) algorithms","","",&bShowHelpA,0);
  AddParmBool(&parmHelp,"-helpalg,-hw","list of available (weighted) algorithms","","",&bShowHelpW,0);
  AddParmBool(&parmHelp,"-helpreports,-hr","list all reports","","",&bShowHelpR,0);
  AddParmBool(&parmHelp,"-helpcolumns,-hc","help for reports with columns (-r out),(-r rtd)","","",&bShowHelpC,0);
  AddParmBool(&parmHelp,"-helpstats,-hs","help for the statistics report (-r stats)","","",&bShowHelpS,0);
  AddParmBool(&parmHelp,"-helpverbose,-hv","list all parameters and algorithms (verbose)","","",&bShowHelpV,0);
  AddParmBool(&parmHelp,"-helpterse,-ht","list all parameters and algorithms (terse)","","",&bShowHelpT,0);

  AddParmUInt(&parmUBCSAT,"-runs","number of independent attempts (runs) [default %s]","","",&iNumRuns,1);
  AddParmUBigInt(&parmUBCSAT,"-cutoff","maximum number of search steps per run [default %s]","you can specify \"-cutoff max\" for largest integer limit","",&iCutoff,100000);
  AddParmFloat(&parmUBCSAT,"-timeout","maximum number of seconds per run","each run will terminate unsuccessfully after FL seconds,~or when the -cutoff is reached: whichever happens first~so use \"-cutoff max\" to ensure timeout times are reached","CheckTimeout",&fTimeOut,FLOATZERO);
  AddParmFloat(&parmUBCSAT,"-gtimeout","global timeout: maximum number of seconds for all runs","the current run and all remaining runs will terminate~after FL seconds","CheckTimeout",&fGlobalTimeOut,FLOATZERO);
  AddParmBool(&parmUBCSAT,"-abstime","use absolute time (incl. startup) for global timeout","if true [1] timestamp is taken at startup~otherwise, it's taken after initialization","",&bUseAbsoluteTime,0);
  AddParmBool(&parmUBCSAT,"-systime","include system time for timing information","if true [1] both user and system time are used for timing~otherwise, just user time is used","",&bUseSystemTime,0);
  AddParmUInt(&parmUBCSAT,"-timeres","time resolution: check timer every INT search steps","number of search steps that will elapse~between checks for timeouts [default %s]","",&iTimeResolution,1000);
  AddParmUBigInt(&parmUBCSAT,"-noimprove","terminate run if no improvement in INT steps","if no improvement in the solution quality has been made~in INT steps, then the run will terminate~(for solution quality description see -target and -wtarget)","NoImprove",&iNoImprove,0);

  AddParmUBigInt(&parmUBCSAT,"-earlysteps","terminate run early after INT steps","if after INT steps the solution quality is greater than~the value specified in -earlyqual the run will terminate~(for solution quality description see -target and -wtarget)","EarlyTerm",&iEarlyTermSteps,0);
  AddParmUInt(&parmUBCSAT,"-earlyqual","terminate run early if quality is worse than INT","(see -earlysteps)","EarlyTerm",&iEarlyTermQual,0);
  AddParmUBigInt(&parmUBCSAT,"-earlywqual","terminate run early if weighted quality is worse than INT","(see -earlysteps and -earlyqual)","EarlyTerm",&iEarlyTermQualWeight,0);
  AddParmUInt(&parmUBCSAT,"-strikes","terminate all runs after INT unsuccessful runs","","Strikes",&iStrikes,0);
  
  AddParmUInt(&parmUBCSAT,"-target","target solution quality","for regular (unweighted) algorithms, the solution quality~is measured as the number of false clauses~~for MAX-SAT (or for some other reason) you can set~the desired solution quality so that solution is found if~the number false clauses <= target~~default target solution quality is zero (no false clauses)","",&iTarget,0);
  AddParmUBigInt(&parmUBCSAT,"-wtarget","weighted target solution quality","similar to -target, except the solution quality is the~sum of the weights of the false clauses","",&iTargetWeight,0);
  
  AddParmUInt(&parmUBCSAT,"-seed","specify an initial random seed","","",&iSeed,iSeed);
  
  AddParmBool(&parmUBCSAT,"-solve","stop when a solution has been found and print solution","-solve may not complete all (-runs) specified~-solve also turns on the model report (-r model)","SolveMode",&bSolveMode,0);
  AddParmUInt(&parmUBCSAT,"-find,-numsol","terminate after INT successful runs","-find may not complete all (-runs) specified~or may terminate before enough successful runs","",&iFind,0);
  AddParmUInt(&parmUBCSAT,"-findunique","terminate after INT unique solutions have been found","-findunique may not complete all (-runs) specified~or may terminate before enough unique successful runs","UniqueSolutions",&iFindUnique,0);
  
  AddParmUInt(&parmUBCSAT,"-srestart","static (periodic) restart every INT steps","in UBCSAT restarts do not terminate a run, and several~restarts can occur within a single run","CheckForRestarts",&iPeriodicRestart,0);
  AddParmProbability(&parmUBCSAT,"-prestart","probabilistically restart at each step with probability PR","","CheckForRestarts",&iProbRestart,FLOATZERO);
  AddParmUInt(&parmUBCSAT,"-drestart","dynamic restart if no improvement in INT steps","similar to (-noimprove), except that -drestart restarts~the algorithm within the run instead of terminating the run","CheckForRestarts,BestFalse",&iStagnateRestart,0);

  AddParmString(&parmIO,"-inst,-i","specify input instance file: (.cnf) or (.wcnf) format","if no file is specified, then UBCSAT reads from stdin~example: ubcsat < sample.cnf","",&sFilenameIn,"");

  AddParmString(&parmIO,"-varinitfile","variable initialization file","variables are initialized to specific values at the~start of each run and at restarts~~Example file:~  -1 3 -4 9 ~sets variables (3,9) to true and variables (1,4) to false~and all other variables would be initialized randomly","",&sFilenameVarInit,"");
  AddParmUInt(&parmIO,"-varinitflip","flip INT variables after initialization","forces INT (unique) random variables to be flipped~after initialization","CandidateList",&iInitVarFlip,0);
  AddParmBool(&parmIO,"-varinitgreedy","greedy variable initialization","if a variable appears more often as a positive literal~then the var is initialized to true (and vice-versa)~for vars with ties, it alternates between true and false~this initialization is deterministic","",&bVarInitGreedy,0);

  AddParmString(&parmIO,"-param,-fp","read command-line parameters from a file","file format is plain text, and in command-line syntax~the command-line will override any parameters from files~and you can specify more than one file~~Example file:~  -runs 100 -cutoff max -noimprove 1000n","",&sFilenameParms,"");

  AddParmReport(&parmIO,"-report,-r","-r reportname [filename [params]]... use -hr for more info","","");

  AddParmBool(&parmIO, "-recho","all reports directed to files will also be echoed to stdout","","",&bReportEcho,0);
  AddParmBool(&parmIO, "-rflush","all report buffers are flushed before each run","","FlushBuffers",&bReportFlush,0);
  AddParmBool(&parmIO, "-rclean","suppress all report header output","","",&bReportClean,0);
  AddParmBool(&parmIO, "-rcsv","use alternate CSV format for (most) reports","","SetupCSV",&bReportCSV,0);

  AddParmBool(&parmIO, "-q","quiet mode (turn (-r out) and (-r stats) off by default)","","",&bReportQuiet,0);

  AddParmString(&parmIO, "-rcomment","specify comment character for report headers (# is default)","","",&sCommentString,"#");

  AddParmString(&parmIO,"-filesol,-fs","specify a file with known solutions","(for FDC calc, distance report, etc...)~file format is same as output from (-r uniquesol)","LoadKnownSolutions",&sFilenameSoln,"");

  AddParmString(&parmIO,"-filerand,-fr","specify a file to read random bits from","can be used instead of a pseudo-random number generator~reads 32 bits of random data at a time, and will loop~back to the start of the file if it runs out of bits~file format is binary","FileRandom",&sFilenameRandomData,"");

  AddParmString(&parmIO,"-fileabort,-fa","specify a signal file to terminate all remaining runs","during a long execution with numerous runs, you can create~an abort file (the contents of the file are not important)~to prevent any remaining runs from starting...~the current run will finish and all reports will finish","FileAbort",&sFilenameAbort,"");

}

#ifdef __cplusplus

}
#endif
