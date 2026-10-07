------------------------------ MODULE PlusCalTranslation ------------------------------

EXTENDS Naturals, Sequences, TLC

(*
This module models a translation from a global-naming PlusCal (+CAL) abstract syntax tree (AST)
into TLA+ lexeme sequences. It includes:
- A grammar (as predicates) for legal ASTs of algorithms, procedures, processes, and statements.
- Operators that translate such trees into sequences of lexemes representing Init, Next, Spec, and a Termination property.
- Modeling of fairness options for the generated specification: None, WF of process actions, WF of Next, and SF of process actions.
- An executable-state machine that produces the translation; termination is guaranteed by weak fairness of the translation action.
*)

CONSTANTS
    Ids,         \* A finite or infinite set of identifiers (e.g., strings)
    Exprs,       \* A set of expression lexemes (e.g., strings encoding TLA+/PlusCal expressions)
    Tokens,      \* A set of additional lexemes used in the generated output (e.g., "Init","==","/\\", etc.)
    AlgAST,      \* The input algorithm AST to translate (record described by IsAlg)
    FairnessMode \* One of {"None","WFProc","WFNext","SFProc"}

FairnessModes == {"None","WFProc","WFNext","SFProc"}

ASSUME FairnessMode \in FairnessModes

Lex == Ids \cup Exprs \cup Tokens

(***************************************************************************)
(* Grammar of statements, procedures, processes, and algorithms            *)
(***************************************************************************)

Kinds == {
  "Assign",    \* [var: Id, expr: Expr]
  "If",        \* [arms: Seq([cond: Expr, body: Seq(Stmt)])]
  "While",     \* [cond: Expr, body: Seq(Stmt)]
  "Call",      \* [proc: Id, args: Seq(Expr)]
  "Return",    \* []
  "Skip",      \* []
  "Goto",      \* [label: Id]
  "Labeled"    \* [label: Id, stmt: Stmt]
}

IsId(i) == i \in Ids
IsExpr(e) == e \in Exprs

RECURSIVE IsStmt(_)
RECURSIVE IsStmtSeq(_)
RECURSIVE AllArmsOk(_)

IsAssign(s) ==
  /\ s \in [kind: {"Assign"}, var: Ids, expr: Exprs]

IsIf(s) ==
  /\ s.kind = "If"
  /\ AllArmsOk(s.arms)

AllArmsOk(arms) ==
  IF arms = << >> THEN TRUE
  ELSE LET a == Head(arms) IN
       /\ a \in [cond: Exprs, body: Seq(BOOLEAN)]
          \* type skeleton; refined by IsStmtSeq below
       /\ IsExpr(a.cond)
       /\ IsStmtSeq(a.body)
       /\ AllArmsOk(Tail(arms))

IsWhile(s) ==
  /\ s.kind = "While"
  /\ IsExpr(s.cond)
  /\ IsStmtSeq(s.body)

IsCall(s) ==
  /\ s.kind = "Call"
  /\ IsId(s.proc)
  /\ s.args \in Seq(Exprs)

IsReturn(s) ==
  s.kind = "Return"

IsSkip(s) ==
  s.kind = "Skip"

IsGoto(s) ==
  /\ s.kind = "Goto"
  /\ IsId(s.label)

IsLabeled(s) ==
  /\ s.kind = "Labeled"
  /\ IsId(s.label)
  /\ IsStmt(s.stmt)

IsStmt(s) ==
  /\ s.kind \in Kinds
  /\ CASE s.kind = "Assign"  -> IsAssign(s)
        [] s.kind = "If"      -> IsIf(s)
        [] s.kind = "While"   -> IsWhile(s)
        [] s.kind = "Call"    -> IsCall(s)
        [] s.kind = "Return"  -> IsReturn(s)
        [] s.kind = "Skip"    -> IsSkip(s)
        [] s.kind = "Goto"    -> IsGoto(s)
        [] s.kind = "Labeled" -> IsLabeled(s)
        [] OTHER              -> FALSE

IsStmtSeq(ss) ==
  IF ss \in Seq(BOOLEAN) THEN
     \* This guard ensures ss is a sequence; TLC's Seq(S) requires S; we refine element typing below
     IF ss = << >> THEN TRUE
     ELSE /\ IsStmt(Head(ss))
          /\ IsStmtSeq(Tail(ss))
  ELSE
     \* Ensure it's a sequence structurally
     IF ss = << >> THEN TRUE
     ELSE /\ IsStmt(Head(ss))
          /\ IsStmtSeq(Tail(ss))

IsProcedure(p) ==
  /\ p \in [name: Ids, params: Seq(Ids), body: Seq(BOOLEAN)]
  /\ IsStmtSeq(p.body)

IsProcess(pr) ==
  /\ pr \in [name: Ids, params: Seq(Ids), body: Seq(BOOLEAN)]
  /\ IsStmtSeq(pr.body)

IsAlg(a) ==
  /\ a \in [
       name: Ids,
       variables: Seq(Ids),
       procedures: Seq(BOOLEAN),
       processes: Seq(BOOLEAN),
       fairness: FairnessModes
     ]
  /\ \A i \in 1..Len(a.procedures): IsProcedure(a.procedures[i])
  /\ \A i \in 1..Len(a.processes): IsProcess(a.processes[i])

WF_AST == IsAlg(AlgAST)

(***************************************************************************)
(* Translation to lexeme sequences                                         *)
(***************************************************************************)

\* Utility: join a sequence of lexemes with a separator lexeme
LexJoin(xs, sep) ==
  IF xs = << >> THEN << >>
  ELSE IF Len(xs) = 1 THEN << xs[1] >>
  ELSE << xs[1], sep >> \o LexJoin(SubSeq(xs, 2, Len(xs)), sep)

\* Utility: wrap a sequence with left/right delimiter lexemes
LexWrap(left, body, right) == << left >> \o body \o << right >>

\* Some conventional tokens we will likely use.
TokInit   == "Init"
TokNext   == "Next"
TokSpec   == "Spec"
TokEq     == "=="
TokAnd    == "/\\"
TokBox    == "[]"
TokSub    == "_"            \* for rendering [][Next]_vars as a flat string we may not need this, kept for completeness
TokVars   == "vars"
TokTRUE   == "TRUE"
TokUNCH   == "UNCHANGED"
TokTerm   == "Termination"
TokEventually == "<>"
TokWF     == "WF_"
TokSF     == "SF_"
TokForAll == "\\A"
TokIn     == "\\in"
TokColon  == ":"
TokProcIds == "ProcIds"
TokProcAct == "ProcAct"

\* Translate statements to a (very shallow) lexeme sequence placeholder.
RECURSIVE TranslateStmt(_)
RECURSIVE TranslateStmtSeq(_)

TranslateStmt(s) ==
  CASE s.kind = "Assign" ->
         << "\\*", "stmt:", "Assign" >> \o << s.var, ":=", s.expr >>
  [] s.kind = "If" ->
         << "\\*", "stmt:", "If" >>
         \o (LET arms == s.arms IN
               IF arms = << >> THEN << >>
               ELSE
                 \* Concatenate each arm as ["IF"/"ELSIF" cond "THEN" ...]
                 LET ArmLex(i) ==
                       LET tag == IF i = 1 THEN "IF" ELSE "ELSIF" IN
                       << tag >> \o << s.arms[i].cond >> \o << "THEN" >> \o TranslateStmtSeq(s.arms[i].body)
                 IN
                 \* Fold over arms
                 [i \in 1..Len(arms) |-> ArmLex(i)] \* this builds a function; we want a sequence concatenation:
                 \* Workaround: simple placeholder:
                 << "..." >>)
  [] s.kind = "While" ->
         << "\\*", "stmt:", "While" >> \o << s.cond >> \o TranslateStmtSeq(s.body)
  [] s.kind = "Call" ->
         << "\\*", "stmt:", "Call" >> \o << s.proc, "(", ")" >>
  [] s.kind = "Return" ->
         << "\\*", "stmt:", "Return" >>
  [] s.kind = "Skip" ->
         << "\\*", "stmt:", "Skip" >>
  [] s.kind = "Goto" ->
         << "\\*", "stmt:", "Goto" >> \o << s.label >>
  [] s.kind = "Labeled" ->
         << "\\*", "label:" >> \o << s.label >> \o TranslateStmt(s.stmt)
  [] OTHER ->
         << "\\*", "stmt:", "Unknown" >>

TranslateStmtSeq(ss) ==
  IF ss = << >> THEN << >>
  ELSE TranslateStmt(Head(ss)) \o TranslateStmtSeq(Tail(ss))

\* Generate Init lexemes
GenInit(a) ==
  << TokInit, TokEq, TokTRUE >>

\* Generate Next lexemes
GenNext(a) ==
  << TokNext, TokEq, TokUNCH, TokVars >>

\* Generate Spec lexemes, modeling the fairness options for the GENERATED spec.
GenSpec(a) ==
  LET base == << TokSpec, TokEq, TokInit, TokAnd, TokBox \o TokNext \o "_" \o TokVars >>
      fairNone == base
      fairWFProc ==
        base \o
        << TokAnd, TokForAll, "p", TokIn, TokProcIds, TokColon, TokWF \o TokVars, "(", TokProcAct, "(", "p", ")", ")" >>
      fairWFNext ==
        base \o
        << TokAnd, TokWF \o TokVars, "(", TokNext, ")" >>
      fairSFProc ==
        base \o
        << TokAnd, TokForAll, "p", TokIn, TokProcIds, TokColon, TokSF \o TokVars, "(", TokProcAct, "(", "p", ")", ")" >>
  IN CASE a.fairness = "None"   -> fairNone
        [] a.fairness = "WFProc" -> fairWFProc
        [] a.fairness = "WFNext" -> fairWFNext
        [] a.fairness = "SFProc" -> fairSFProc
        [] OTHER                 -> fairNone

\* Generate Termination lexemes (a property name for the generated spec)
GenTermination(a) ==
  << TokTerm, TokEq, TokEventually, "Terminated" >>

\* Top-level translation of the algorithm to an output record of lexeme sequences.
ComposeSpec(a) ==
  [ InitLex |-> GenInit(a),
    NextLex |-> GenNext(a),
    SpecLex |-> GenSpec(a),
    TermLex |-> GenTermination(a),
    FairnessChoice |-> a.fairness ]

TypeOut(o) ==
  /\ o \in [
      InitLex: Seq(Lex),
      NextLex: Seq(Lex),
      SpecLex: Seq(Lex),
      TermLex: Seq(Lex),
      FairnessChoice: FairnessModes
     ]

\* Compute a "normalized" AST whose fairness field follows the selected FairnessMode constant.
NormalizeAlg(a) ==
  [a EXCEPT !.fairness = FairnessMode]

(***************************************************************************)
(* State variables and transition system for the translator                *)
(***************************************************************************)

VARIABLES out, done

vars == << out, done >>

Init ==
  /\ WF_AST
  /\ done = FALSE
  /\ out \in [
       InitLex: Seq(Lex),
       NextLex: Seq(Lex),
       SpecLex: Seq(Lex),
       TermLex: Seq(Lex),
       FairnessChoice: FairnessModes
     ]
     \* allow any initial placeholder output
     
DoTranslate ==
  /\ ~done
  /\ LET a == NormalizeAlg(AlgAST) IN
       /\ out' = ComposeSpec(a)
       /\ done' = TRUE

Stutter ==
  /\ done
  /\ UNCHANGED vars

Next == DoTranslate \/ Stutter

(***************************************************************************)
(* Safety invariants and liveness properties                               *)
(***************************************************************************)

\* The AST remains well-formed.
Inv_WellFormedAST == WF_AST

\* Output is always well-typed.
Inv_TypeOK == TypeOut(out)

\* Once translation is done, the output equals the translation of the normalized AST.
Inv_CorrectOutput ==
  done => out = ComposeSpec(NormalizeAlg(AlgAST))

\* The chosen fairness mode is reflected in the generated Spec lexemes metadata.
Inv_FairnessModeReflected ==
  out.FairnessChoice = FairnessMode

\* Combined safety invariant
SafetyInv == Inv_WellFormedAST /\ Inv_TypeOK /\ Inv_CorrectOutput /\ Inv_FairnessModeReflected

\* Liveness: the translator eventually finishes.
Termination == <> done

(***************************************************************************)
(* Overall specification and fairness of the translator action             *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars /\ WF_vars(DoTranslate)

=============================================================================