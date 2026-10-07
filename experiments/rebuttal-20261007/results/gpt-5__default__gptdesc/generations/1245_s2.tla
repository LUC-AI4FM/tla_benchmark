---- MODULE PlusCalASTTranslation ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
  Proc, \* Finite set of process identifiers
  GlobalVars, \* Finite set of global variable names
  LocalVars, \* Finite set of local variable names
  Val, \* Finite nonempty set of values
  StartLbl, \* Function [Proc -> Nat] providing each process start label
  ExitLbl, \* Function [Proc -> Nat] providing each process exit label
  SrcAST, \* Input abstract syntax tree (AST) to translate
  FairnessMode \* One of {"None","WFProc","WFNext","SFProc"}

VARIABLES
  stage,
  srcAST,
  explodedAST,
  resolvedAST,
  subscriptedAST,
  pc, \* output runtime variable: program counter per process
  done, \* output runtime variable: termination flag per process
  gmem, \* output runtime variable: mapping global vars to values
  lmem \* output runtime variable: mapping proc -> (local var -> value)

Tags == {"Assign","Goto","Call","Return","If","While","Skip"}
StructuredTags == {"If","While"}
JumpCallTags == {"Goto","Call","Return"}

StmtSet == [type: Tags, label: Nat, body: Seq(Nat)]

IsStmt(s) == s \in StmtSet

IsAST(ast) ==
  /\ ast \in [
        procs: [Proc -> Seq(StmtSet)],
        start: [Proc -> Nat],
        exit:  [Proc -> Nat]
     ]

NoStructured(ast) ==
  /\ IsAST(ast)
  /\ \A p \in Proc:
       \A i \in DOMAIN ast.procs[p]:
         ~(ast.procs[p][i].type \in StructuredTags)

ResolvedCalls(ast) ==
  /\ IsAST(ast)
  /\ \A p \in Proc:
       \A i \in DOMAIN ast.procs[p]:
         ~(ast.procs[p][i].type \in JumpCallTags)

SubscriptedOK(ast) ==
  /\ IsAST(ast)
  /\ TRUE

StageSet == {"Start","Exploded","Resolved","Subscripted","Built"}

EmptyAST ==
  [ procs |-> [p \in Proc |-> <<>>],
    start |-> StartLbl,
    exit  |-> ExitLbl ]

BuildExploded(ast) == EmptyAST
BuildResolved(ast) == EmptyAST
BuildSubscripted(ast) == EmptyAST

Dflt ==
  CHOOSE v \in Val: TRUE

OutInit ==
  /\ pc = StartLbl
  /\ done = [p \in Proc |-> FALSE]
  /\ gmem \in [GlobalVars -> Val]
  /\ lmem \in [p \in Proc |-> [x \in LocalVars |-> Dflt]]

OutNextProcBare(p) ==
  /\ p \in Proc
  /\ ~done[p]
  /\ done' = [done EXCEPT ![p] = TRUE]
  /\ UNCHANGED << pc, gmem, lmem, stage, srcAST, explodedAST, resolvedAST, subscriptedAST >>

OutNextBare ==
  \E p \in Proc: OutNextProcBare(p)

OutVars == << pc, done, gmem, lmem >>

OutFairnessBare ==
  CASE FairnessMode = "None"  -> TRUE
     [] FairnessMode = "WFProc" -> \A p \in Proc: WF_OutVars(OutNextProcBare(p))
     [] FairnessMode = "WFNext" -> WF_OutVars(OutNextBare)
     [] FairnessMode = "SFProc" -> \A p \in Proc: SF_OutVars(OutNextProcBare(p))

OutSpec ==
  /\ OutInit
  /\ [][OutNextBare]_OutVars
  /\ OutFairnessBare

OutNextProc(p) ==
  /\ stage = "Built"
  /\ OutNextProcBare(p)

OutNext ==
  \E p \in Proc: OutNextProc(p)

PipelineStep ==
  \/ /\ stage = "Start"
     /\ stage' = "Exploded"
     /\ explodedAST' = BuildExploded(srcAST)
     /\ UNCHANGED << srcAST, resolvedAST, subscriptedAST, pc, done, gmem, lmem >>
  \/ /\ stage = "Exploded"
     /\ stage' = "Resolved"
     /\ resolvedAST' = BuildResolved(explodedAST)
     /\ UNCHANGED << srcAST, explodedAST, subscriptedAST, pc, done, gmem, lmem >>
  \/ /\ stage = "Resolved"
     /\ stage' = "Subscripted"
     /\ subscriptedAST' = BuildSubscripted(resolvedAST)
     /\ UNCHANGED << srcAST, explodedAST, resolvedAST, pc, done, gmem, lmem >>
  \/ /\ stage = "Subscripted"
     /\ stage' = "Built"
     /\ UNCHANGED << srcAST, explodedAST, resolvedAST, subscriptedAST, pc, done, gmem, lmem >>

Init ==
  /\ stage = "Start"
  /\ srcAST = SrcAST
  /\ explodedAST = EmptyAST
  /\ resolvedAST = EmptyAST
  /\ subscriptedAST = EmptyAST
  /\ OutInit

Next ==
  \/ PipelineStep
  \/ OutNext

FairnessModes == {"None","WFProc","WFNext","SFProc"}

FairnessConj ==
  /\ FairnessMode \in FairnessModes
  /\ CASE FairnessMode = "None"  -> TRUE
     [] FairnessMode = "WFProc" -> \A p \in Proc: WF_OutVars(OutNextProc(p))
     [] FairnessMode = "WFNext" -> WF_OutVars(OutNext)
     [] FairnessMode = "SFProc" -> \A p \in Proc: SF_OutVars(OutNextProc(p))

Spec ==
  /\ Init
  /\ [][Next]_<<stage, srcAST, explodedAST, resolvedAST, subscriptedAST, pc, done, gmem, lmem>>
  /\ FairnessConj

AstWellFormedInv ==
  /\ IsAST(EmptyAST)
  /\ IsAST(explodedAST)
  /\ IsAST(resolvedAST)
  /\ IsAST(subscriptedAST)

StageInvariant ==
  stage \in StageSet

ExplosionInvariant ==
  stage \in {"Exploded","Resolved","Subscripted","Built"} => NoStructured(explodedAST)

ResolutionInvariant ==
  stage \in {"Resolved","Subscripted","Built"} => ResolvedCalls(resolvedAST)

SubscriptInvariant ==
  stage \in {"Subscripted","Built"} => SubscriptedOK(subscriptedAST)

Termination ==
  <> (\A p \in Proc: done[p])

BuiltEventually ==
  <> (stage = "Built")

====