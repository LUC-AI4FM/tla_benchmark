------------------------------ MODULE PlusCalAST2TLA ------------------------------

EXTENDS Naturals, Sequences, TLC

CONSTANTS
    InputAST,
    FairnessOpt

(*
  Basic lexical domain for generated output.
*)
Lexeme == STRING

(*
  Utilities
*)
IsStrSeq(s) ==
  /\ IsSeq(s)
  /\ \A i \in 1..Len(s): s[i] \in STRING

Contains(seq, x) == IsSeq(seq) /\ (\E i \in 1..Len(seq): seq[i] = x)

(*
  AST grammar predicates (global-naming PlusCal, simplified).
  We model a minimal but faithful shape sufficient for translation.
*)

(*
  Forward declarations (mutual recursion of grammar predicates).
*)
IsStmt(st) == 
  /\ st /= st  \* always FALSE placeholder to allow forward references; real def appears below
IsLStmt(ls) == 
  /\ ls /= ls  \* always FALSE placeholder; real def appears below
IsLStmtSeq(S) ==
  /\ IsSeq(S)
  /\ \A i \in 1..Len(S): IsLStmt(S[i])
IsProcedure(p) ==
  /\ p /= p \* placeholder; real def appears below
IsProcess(pr) ==
  /\ pr /= pr \* placeholder; real def appears below
IsAlgorithm(a) ==
  /\ a /= a \* placeholder; real def appears below

(*
  Concrete grammar predicates.
*)
IsStmt(st) ==
  /\ DOMAIN st = {"kind","args"}
  /\ st.kind \in {"Skip","Assign","Goto","If"}
  /\ CASE st.kind = "Skip" ->
         st.args \in STRING
     [] st.kind = "Assign" ->
         /\ DOMAIN st.args = {"lhs","rhs"}
         /\ st.args.lhs \in STRING
         /\ st.args.rhs \in STRING
     [] st.kind = "Goto" ->
         /\ DOMAIN st.args = {"label"}
         /\ st.args.label \in STRING
     [] st.kind = "If" ->
         /\ DOMAIN st.args = {"cond","then","else"}
         /\ st.args.cond \in STRING
         /\ IsLStmtSeq(st.args.then)
         /\ IsLStmtSeq(st.args.else)

IsLStmt(ls) ==
  /\ DOMAIN ls = {"kind","label","stmt"}
  /\ ls.kind = "LStmt"
  /\ ls.label \in STRING
  /\ IsStmt(ls.stmt)

IsProcedure(p) ==
  /\ DOMAIN p = {"kind","name","params","body"}
  /\ p.kind = "Proc"
  /\ p.name \in STRING
  /\ IsStrSeq(p.params)
  /\ IsLStmtSeq(p.body)

IsProcess(pr) ==
  /\ DOMAIN pr = {"kind","name","params","body"}
  /\ pr.kind = "Process"
  /\ pr.name \in STRING
  /\ IsStrSeq(pr.params)
  /\ IsLStmtSeq(pr.body)

IsProcedureSeq(S) ==
  /\ IsSeq(S)
  /\ \A i \in 1..Len(S): IsProcedure(S[i])

IsProcessSeq(S) ==
  /\ IsSeq(S)
  /\ \A i \in 1..Len(S): IsProcess(S[i])

IsAlgorithm(a) ==
  /\ DOMAIN a = {"kind","name","vars","procedures","processes","body"}
  /\ a.kind = "Alg"
  /\ a.name \in STRING
  /\ IsStrSeq(a.vars)
  /\ IsProcedureSeq(a.procedures)
  /\ IsProcessSeq(a.processes)
  /\ IsLStmtSeq(a.body)

(*
  Translation to lexeme sequences.
  We only model high-level structural emission sufficient to capture Init, Next, Spec,
  Termination, and fairness clauses. On ill-formed ASTs, we emit a single ERROR token.
*)

TranslateInit(a) ==
  IF IsAlgorithm(a)
  THEN <<"Init","==","TRUE">>
  ELSE <<"ERROR:IllFormedAlg">>

TranslateNext(a) ==
  IF IsAlgorithm(a)
  THEN <<"Next","==","TRUE">>
  ELSE <<"ERROR:IllFormedAlg">>

TranslateSpec(a, f) ==
  IF ~IsAlgorithm(a) THEN <<"ERROR:IllFormedAlg">>
  ELSE
    LET base == <<"Spec","==","Init","/\\","[Next]_V">>
        fair ==
          CASE f = "None"    -> <<>>
             [] f = "WF_Next"-> <<"/\\","WF_vars(DoProc)">>
             [] f = "WF_Proc"-> <<"/\\","WF_ProcActions">>
             [] f = "SF_Proc"-> <<"/\\","SF_ProcActions">>
             [] OTHER         -> <<"/\\","UNKNOWN_FAIRNESS">>
    IN base \o fair

TranslateTerm(a) ==
  IF IsAlgorithm(a)
  THEN <<"Termination","==","<>","done">>
  ELSE <<"ERROR:IllFormedAlg">>

TranslateAll(a, f) ==
  IF ~IsAlgorithm(a) THEN <<"ERROR:IllFormedAlg">>
  ELSE TranslateInit(a) \o TranslateNext(a) \o TranslateSpec(a, f) \o TranslateTerm(a)

(*
  Runtime state of the translator as an executable specification.
*)
VARIABLES out, done, phase

V == << out, done, phase >>

PhaseSet == {"start","emitInit","emitNext","emitSpec","emitTerm","done"}

Init ==
  /\ out = << >>
  /\ done = FALSE
  /\ phase = "start"

DoInit ==
  /\ phase = "start"
  /\ IsAlgorithm(InputAST)
  /\ out' = out \o TranslateInit(InputAST)
  /\ done' = FALSE
  /\ phase' = "emitNext"

DoNext ==
  /\ phase = "emitNext"
  /\ IsAlgorithm(InputAST)
  /\ out' = out \o TranslateNext(InputAST)
  /\ done' = FALSE
  /\ phase' = "emitSpec"

DoSpec ==
  /\ phase = "emitSpec"
  /\ IsAlgorithm(InputAST)
  /\ out' = out \o TranslateSpec(InputAST, FairnessOpt)
  /\ done' = FALSE
  /\ phase' = "emitTerm"

DoTerm ==
  /\ phase = "emitTerm"
  /\ IsAlgorithm(InputAST)
  /\ out' = out \o TranslateTerm(InputAST)
  /\ done' = TRUE
  /\ phase' = "done"

Stutter ==
  /\ out' = out
  /\ done' = done
  /\ phase' = phase

DoProc == DoInit \/ DoNext \/ DoSpec \/ DoTerm

Next == DoProc \/ Stutter

AllowedFairness == {"None","WF_Proc","WF_Next","SF_Proc"}

FairnessConj ==
  CASE FairnessOpt = "None"    -> TRUE
     [] FairnessOpt = "WF_Next"-> WF_V(DoProc)
     [] FairnessOpt = "WF_Proc"-> /\ WF_V(DoInit) /\ WF_V(DoNext) /\ WF_V(DoSpec) /\ WF_V(DoTerm)
     [] FairnessOpt = "SF_Proc"-> /\ SF_V(DoInit) /\ SF_V(DoNext) /\ SF_V(DoSpec) /\ SF_V(DoTerm)
     [] OTHER                  -> TRUE

Spec == Init /\ [][Next]_V /\ FairnessConj

(*
  Safety invariants
*)
GrammarOK == IsAlgorithm(InputAST)

FairnessOK == FairnessOpt \in AllowedFairness

OutIsLexemes ==
  /\ IsSeq(out)
  /\ \A i \in 1..Len(out): out[i] \in Lexeme

PhaseOK == phase \in PhaseSet

DoneImpliesPhase == done => phase = "done"

DoneImpliesFullOutput ==
  done => out = TranslateAll(InputAST, FairnessOpt)

(*
  The emitted fairness option appears in the output when done.
*)
FairnessToken(f) ==
  CASE f = "None"     -> "Spec"
     [] f = "WF_Next" -> "WF_vars(DoProc)"
     [] f = "WF_Proc" -> "WF_ProcActions"
     [] f = "SF_Proc" -> "SF_ProcActions"
     [] OTHER         -> "UNKNOWN_FAIRNESS"

EmittedFairnessCorrect ==
  done => Contains(out, FairnessToken(FairnessOpt))

SafetyInv ==
  /\ GrammarOK
  /\ FairnessOK
  /\ OutIsLexemes
  /\ PhaseOK
  /\ DoneImpliesPhase
  /\ DoneImpliesFullOutput
  /\ EmittedFairnessCorrect

(*
  Liveness
*)
Termination == <>done

=============================================================================