MODULE XPlusCalTranslation
EXTENDS Naturals, Sequences

CONSTANTS AST, FairnessOption

VARIABLES terminated

(* Type predicates *)
IsAlgorithm(a) == a.kind = "Algorithm"
IsProcedure(p) == p.name # ""
IsProcess(pr) == pr.name # ""

(* Translation operator *)
Translation(alg, fairnessOption) ==
  LET
    initSeq == InitSeq(alg)
    nextSeq == NextSeq(alg)
    procSeqs == ProcSeqs(alg)
    processSeqs == ProcessSeqs(alg)
    fairnessClause == FairnessClause(fairnessOption)
  IN
    initSeq \o nextSeq \o procSeqs \o processSeqs \o fairnessClause

InitSeq(a) ==
  IF IsAlgorithm(a) THEN
    "VARIABLES pc, stack\n"
  ELSE ""

NextSeq(a) == ""

ProcSeqs(a) ==
  IF IsAlgorithm(a) THEN
    "\nPROC_DEFINITIONS\n"
  ELSE ""

ProcessSeqs(a) ==
  IF IsAlgorithm(a) THEN
    "\nPROCESS_DEFINITIONS\n"
  ELSE ""

FairnessClause(opt) ==
  IF opt = "" THEN ""
  ELSE IF opt = "wf" THEN "\nWF: ...\n"
  ELSE IF opt = "wfNext" THEN "\nWFNEXT: ...\n"
  ELSE IF opt = "sf" THEN "\nSF: ...\n"
  ELSE ""

(* Explode functions placeholders *)
Explode(stmt) == stmt

(* XlateCall, XlateReturn placeholders *)
XlateCall(call) == ""
XlateReturn(ret) == ""

TerminationLiveness == <> terminated

Init == terminated = FALSE
Next == terminated' = TRUE

Spec == Translation(AST, FairnessOption) /\ TerminationLiveness

ASSUME
  IsAlgorithm(AST)
END MODULE