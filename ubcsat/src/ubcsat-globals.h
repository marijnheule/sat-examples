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

#ifndef UBCSAT_GLOBALS_H
#define UBCSAT_GLOBALS_H

#include "ubcsat-types.h"

#ifdef __cplusplus 
namespace ubcsat {
#endif


/***** UBCSAT GLOBAL VARIABLES *****/
/*
    sAlgName              name of current algorithm
    sVarName              variant name of current algorithm
    bWeighted             does the current algorithm use weighted clauses?

    pActiveAlgorithm      the active algorithm for this session of UBCSAT

    iNumRuns              total number of runs
    iCutoff               step cutoff for each run
    fTimeOut              timeout per runs in seconds
    fGlobalTimeOut        timeout for all runs in seconds
    iSeed                 initial seed for the system

    iTarget               target solution quality (# of false clauses)
    iTargetWeight         weighted target solution quality (sum of false clause weights)

    iFlipCandidate        current variable to flip

    iFind                 total number of solutions to find
    iNumSolutionsFound    number of solutions found so far

    iFindUnique           # of unique solutions to find
    
    iPeriodicRestart      restart each run every iPeriodicRestart steps
    iProbRestart          restart with a probability
    iStagnateRestart      restart if no improvement in iStagnateRestart steps

    bRestart              flag to restart the current run

    iRun                  current run number
    iStep                 current step number

    bTerminateAllRuns     flag to terminate all runs
    bSolutionFound        flag to indicate target solution quality found this run 
    bTerminateRun         flag to terminate this run

    bSolveMode            flag to indicate "solve mode"

    sFilenameIn           file name of instance
    sFilenameParms        file name of current parameter file (note, can be multiple files)
    sFilenameVarInit      file name of variable initialization file

    bReportEcho           flag to set all file output to screen
    bReportFlush          flush all reports before each run
    bReportClean          flag to remove headers from output

    iBestScore            value of best score improvement this step
    iBestScoreWeight      value of best weighted score improvement this step
*/

extern const char sNull;

extern char *sAlgName;
extern char *sVarName;
extern BOOL bWeighted;

extern ALGORITHM *pActiveAlgorithm;

extern UINT32 iNumRuns;
extern UBIGINT iCutoff;
extern FLOAT fTimeOut;
extern FLOAT fGlobalTimeOut;
extern UINT32 iSeed;

extern UINT32 iTarget;
extern UBIGINT iTargetWeight;

extern UINT32 iFlipCandidate;

extern UINT32 iFind;
extern UINT32 iNumSolutionsFound;
extern UINT32 iFindUnique;
extern UINT32 iPeriodicRestart;
extern PROBABILITY iProbRestart;
extern UINT32 iStagnateRestart;

extern BOOL bRestart;

extern UINT32 iRun;
extern UBIGINT iStep;

extern BOOL bTerminateAllRuns;
extern BOOL bSolutionFound;
extern BOOL bTerminateRun;

extern BOOL bSolveMode;

extern char *sFilenameIn;
extern char *sFilenameParms;
extern char *sFilenameVarInit;

extern BOOL bReportEcho;
extern BOOL bReportClean;
extern BOOL bReportFlush;
extern BOOL bReportQuiet;
extern BOOL bReportCSV;

extern SINT32 iBestScore;
extern SBIGINT iBestScoreWeight;


/***** UBCSAT GLOBAL ROUTINES *****/

/*
    CreateAlgorithm()     add a new algorithm to the UBCSAT system
*/

ALGORITHM *CreateAlgorithm (const char *sName, const char *sVariant, BOOL bWeighted, 
                            const char *sDescription, 
                            const char *sAuthors,
                            const char *sHeuristicTriggers,
                            const char *sDataTriggers,
                            const char *sDefaultOutput,
                            const char *sDefaultStats);


/*
    CopyParameters()      copy the parameters from one algorithm to another
*/

void CopyParameters(ALGORITHM *pDest, const char *sName, const char *sVar, BOOL bWeighted);

/*
    InheritDataTriggers()   copy the data triggers from one algorithm to another
*/

void InheritDataTriggers(ALGORITHM *pDest, const char *sName, const char *sVar, BOOL bWeighted);

/*
    CreateTrigger()       add a new trigger to the UBCSAT system
*/

void CreateTrigger(const char *sID,
                   enum EVENTPOINT eEventPoint,
                   FXNPTR pProcedure,
                   const char *sDependencyList,
                   const char *sDeactivateList);

/*
    CreateContainerTrigger()    add a new container trigger to the UBCSAT system
*/

void CreateContainerTrigger(const char *sID, const char *sList);


/*  
    ActivateTriggers()     Explicitly Activate specific trigger(s) [not normally necessary]
*/

void ActivateTriggers(const char *sTriggers);

/*  
    DeActivateTriggers()   Explicitly DeActivate specific trigger(s) [not normally necessary]
*/

void DeActivateTriggers(const char *sTriggers);


/*
    AddParm????()         adds a parameter to an algorithm (many different types)
*/


void AddParmProbability(ALGPARMLIST *pParmList,
                  const char *sSwitch, 
                  const char *sName, 
                  const char *sDescription,
                  const char *sTriggers,
                  PROBABILITY *pProb,
                  FLOAT fProb);

void AddParmUInt(ALGPARMLIST *pParmList, 
                  const char *sSwitch, 
                  const char *sName, 
                  const char *sDescription,
                  const char *sTriggers,
                  UINT32 *pInt,
                  UINT32 iDefInt);

void AddParmUBigInt(ALGPARMLIST *pParmList, 
                  const char *sSwitch, 
                  const char *sName, 
                  const char *sDescription,
                  const char *sTriggers,
                  UBIGINT *pBigInt,
                  UBIGINT iDefBigInt);

void AddParmSInt(ALGPARMLIST *pParmList, 
                  const char *sSwitch, 
                  const char *sName, 
                  const char *sDescription,
                  const char *sTriggers,
                  SINT32 *pSInt,
                  SINT32 iDefSInt);

void AddParmBool(ALGPARMLIST *pParmList, 
                  const char *sSwitch, 
                  const char *sName, 
                  const char *sDescription,
                  const char *sTriggers,
                  BOOL *pBool,
                  BOOL bDefBool);

void AddParmFloat(ALGPARMLIST *pParmList, 
                  const char *sSwitch, 
                  const char *sName, 
                  const char *sDescription,
                  const char *sTriggers,
                  FLOAT *pFloat,
                  FLOAT fDefFloat);

void AddParmString(ALGPARMLIST *pParmList, 
                  const char *sSwitch, 
                  const char *sName, 
                  const char *sDescription,
                  const char *sTriggers,
                  char **pString,
                  const char *sDefString);

                  
/*
    CreateReport()        add a new report to the system
*/

REPORT *CreateReport(const char *sID, 
                     const char *sDescription, 
                     const char *sVerboseDescription, 
                     const char *sOutputFile, 
                     const char *sTriggers);

/*
    AddReportParm???()    add a parameter to a report
*/

void AddReportParmUInt(REPORT *pRep, const char *sParmName, UINT32 *pParmValUInt, UINT32 iDefault);
void AddReportParmBool(REPORT *pRep, const char *sParmName, BOOL *pParmValBool, BOOL bDefault);
void AddReportParmFloat(REPORT *pRep, const char *sParmName, FLOAT *pParmValFloat, FLOAT fDefault);
void AddReportParmString(REPORT *pRep, const char *sParmName, const char *pDefault);

/*
    AddColumn????()       add a column of data for output & rtd reports
*/

void AddColumnUInt(const char *sID, 
                   const char *sDescription, 
                   const char *sHeader1,  
                   const char *sHeader2,  
                   const char *sHeader3, 
                   const char *sPrintFormat, 
                   UINT32 *pCurValue,
                   const char *sTriggers,
                   enum COLTYPE eColType);

void AddColumnUBigInt(const char *sID, 
                   const char *sDescription, 
                   const char *sHeader1,  
                   const char *sHeader2,  
                   const char *sHeader3, 
                   const char *sPrintFormat, 
                   UBIGINT *pCurValue,
                   const char *sTriggers,
                   enum COLTYPE eColType);

void AddColumnFloat(const char *sID, 
                    const char *sDescription, 
                    const char *sHeader1,  
                    const char *sHeader2,  
                    const char *sHeader3, 
                    const char *sPrintFormat,
                    FLOAT *pCurValue,
                    const char *sTriggers,
                    enum COLTYPE eColType);

void AddColumnComposite(const char *sID, 
                        const char *sList);

/*
    AddStatCol()       add a column statistic, providing stats on columns of data 
*/

void AddStatCol(const char *sID, 
             const char *sBaseDescription, 
             const char *sDefParm,
             BOOL bSortByStep);

void AddContainerStat(const char *sID, 
                      const char *sList);

/*
    AddStatCustom()     add a custom statistic, which can be calculated via triggers
*/

void AddStatCustom(const char *sID, 
                   const char *sCustomDescription, 
                   const char *sBaseDescription, 
                   const char *sPrintCustomFormat,
                   void *pCurValue,
                   enum CDATATYPE eCustomType,
                   const char *sDataColumn,
                   const char *sTriggers);


/*
    IsLocalMinimum()      returns TRUE if currently in a local minimum
*/

BOOL IsLocalMinimum(BOOL bUseWeighted);


#ifdef __cplusplus
}
#endif
#endif
