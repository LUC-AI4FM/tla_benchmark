---- MODULE PlusCalAstToTLA ----
EXTENDS Naturals, Sequences, FiniteSets

(*
This module specifies, at the TLA+ level, the translation from the abstract
syntax tree (AST) of a global-naming PlusCal (+CAL) algorithm into a TLA+
specification. It defines the grammar of legal abstract syntax trees for
algorithms, procedures, processes, labeled statements, and related constructs,
and then defines operators that translate such trees into lexeme sequences
(represented here as sequences over Any) representing TLA+ output, including
Init, Next, Spec, and a Termination property. It also models fairness options
for the generated specification: no fairness, weak fairness of process actions,
weak fairness of Next, and strong fairness of process actions.

Notes:
- We keep the AST and the emitted "lexemes" abstract. The set Any is a
  CONSTANT that should be instantiated (e.g., as the set of strings) in a TLC
  configuration. Object is also a CONSTANT, intended to stand for a set of
  JSON-like objects or records, but this spec does not assume any particular
  structure of Object beyond its presence as a CONSTANT.
- The grammar is given as recursive recognizers IsX(...) over values.
- The translation produces sequences of Any intended to be tokens (e.g.,
  strings) forming the text of TLA+ definitions. The translation is schematic
  and intentionally leaves many code-generation details abstract; its purpose
  is to capture structure and fairness handling, not layout or formatting.
*)

CONSTANT Any, Object

(***************************************************************************)
(* Grammar for global-naming PlusCal AST                                   *)
(***************************************************************************)

(*
Identifiers, labels, expressions, and values are abstract and live in Any.
*)

RECURSIVE
  IsStmt(_),
  IsLabeledStmt(_),
  IsStmtSeq(_),
  IsProcedure(_),
  IsProcess(_),
  IsAlgorithm(_),
  JoinWith(_,_),
  EmitStmt(_),
  EmitLabeledStmt(_),
  EmitStmtSeq(_),
  EmitProcedure(_),
  EmitProcess(_),
  EmitInit(_),
  EmitNext(_),
  EmitSpec(_),
  EmitTermination(_),
  EmitAlgorithm(_)

(*
Statement forms (tags):
- "Assign": parallel/multiple assignment
- "If": guarded alternatives, arms = << [cond |-> ..., body |-> StmtSeq], ... >>
- "While": [cond |-> Any, body |-> StmtSeq]
- "Goto": [label |-> Any]
- "Call": [name |-> Any, args |-> Seq(Any)]
- "Return": [value |-> Any] or value omitted (use Any anyway)
- "Skip": no extra fields
- "Either": arms = << StmtSeq, ... >>
- "Await": [cond |-> Any]
- "With": [decls |-> Any, body |-> StmtSeq] (abstract decls)
*)

IsAssign(s) ==
  \E lhs, rhs \in Seq(Any):
    s = [tag |-> "Assign", lhs |-> lhs, rhs |-> rhs] /\ Len(lhs) = Len(rhs)

IsIf(s) ==
  \E arms \in Seq(Any):
    s = [tag |-> "If", arms |-> arms] /\
    \A i \in 1..Len(arms):
      \E c \in Any, b:
        arms[i] = [cond |-> c, body |-> b] /\ IsStmtSeq(b)

IsWhile(s) ==
  \E c \in Any, b:
    s = [tag |-> "While", cond |-> c, body |-> b] /\ IsStmtSeq(b)

IsGoto(s) ==
  \E l \in Any:
    s = [tag |-> "Goto", label |-> l]

IsCall(s) ==
  \E n \in Any, args \in Seq(Any):
    s = [tag |-> "Call", name |-> n, args |-> args]

IsReturn(s) ==
  \E v \in Any:
    s = [tag |-> "Return", value |-> v]

IsSkip(s) ==
  s = [tag |-> "Skip"]

IsEither(s) ==
  \E arms \in Seq(Any):
    s = [tag |-> "Either", arms |-> arms] /\
    \A i \in 1..Len(arms): IsStmtSeq(arms[i])

IsAwait(s) ==
  \E c \in Any:
    s = [tag |-> "Await", cond |-> c]

IsWith(s) ==
  \E d \in Any, b:
    s = [tag |-> "With", decls |-> d, body |-> b] /\ IsStmtSeq(b)

IsStmt(s) ==
  IsAssign(s) \/ IsIf(s) \/ IsWhile(s) \/ IsGoto(s) \/
  IsCall(s) \/ IsReturn(s) \/ IsSkip(s) \/ IsEither(s) \/
  IsAwait(s) \/ IsWith(s)

IsLabeledStmt(ls) ==
  \E l \in Any, st:
    ls = [label |-> l, stmt |-> st] /\ IsStmt(st)

IsStmtSeq(ss) ==
  ss \in Seq(Any) /\ \A i \in 1..Len(ss): IsLabeledStmt(ss[i])

(*
Procedures and processes (global naming):
- Procedure: [tag |-> "Procedure", name |-> Any, params |-> Seq(Any), body |-> StmtSeq]
- Process:   [tag |-> "Process", name |-> Any, self |-> Any, fairness |-> {"None","WF","SF"}, body |-> StmtSeq]
*)

IsProcedure(pr) ==
  \E n \in Any, ps \in Seq(Any), b:
    pr = [tag |-> "Procedure", name |-> n, params |-> ps, body |-> b] /\ IsStmtSeq(b)

IsProcess(pc) ==
  \E n \in Any, self \in Any, f \in {"None","WF","SF"}, b:
    pc = [tag |-> "Process", name |-> n, self |-> self, fairness |-> f, body |-> b] /\ IsStmtSeq(b)

(*
Algorithm root:
[tag |-> "Algorithm",
 name |-> Any,
 vars |-> Seq(Any),
 procedures |-> Seq(Procedure),
 processes |-> Seq(Process),
 fairness |-> {"NoFairness","WFProc","WFNext","SFProc"}]
*)

IsAlgorithm(a) ==
  \E nm \in Any, vs \in Seq(Any), procs \in Seq(Any), procses \in Seq(Any), f \in {"NoFairness","WFProc","WFNext","SFProc"}:
    a = [tag |-> "Algorithm", name |-> nm, vars |-> vs, procedures |-> procs, processes |-> procses, fairness |-> f] /\
    (\A i \in 1..Len(procs): IsProcedure(procs[i])) /\
    (\A j \in 1..Len(procses): IsProcess(procses[j]))

(***************************************************************************)
(* Utilities for lexeme emission (lexemes are Any; e.g., strings)          *)
(***************************************************************************)

(*
JoinWith(sep, xs) joins a flat sequence xs with separator sep.
Elements of xs are tokens (in Any). The result is a flat sequence of tokens.
*)
JoinWith(sep, xs) ==
  IF Len(xs) = 0 THEN << >>
  ELSE IF Len(xs) = 1 THEN << xs[1] >>
  ELSE << xs[1] >> \o << sep >> \o JoinWith(sep, SubSeq(xs, 2, Len(xs)))

(***************************************************************************)
(* Statement emission (schematic, token-level)                             *)
(***************************************************************************)

EmitAssign(s) ==
  \* Emits: "<<Assign>>" as a placeholder for actual assignment translation
  <<"Assign">>

EmitIf(s) ==
  <<"If">>

EmitWhile(s) ==
  <<"While">>

EmitGoto(s) ==
  <<"Goto">>

EmitCall(s) ==
  <<"Call">>

EmitReturn(s) ==
  <<"Return">>

EmitSkip(s) ==
  <<"Skip">>

EmitEither(s) ==
  <<"Either">>

EmitAwait(s) ==
  <<"Await">>

EmitWith(s) ==
  <<"With">>

EmitStmt(s) ==
  CASE IsAssign(s) -> EmitAssign(s)
    [] IsIf(s)     -> EmitIf(s)
    [] IsWhile(s)  -> EmitWhile(s)
    [] IsGoto(s)   -> EmitGoto(s)
    [] IsCall(s)   -> EmitCall(s)
    [] IsReturn(s) -> EmitReturn(s)
    [] IsSkip(s)   -> EmitSkip(s)
    [] IsEither(s) -> EmitEither(s)
    [] IsAwait(s)  -> EmitAwait(s)
    [] IsWith(s)   -> EmitWith(s)
    [] OTHER       -> <<"/* UnknownStmt */">>

EmitLabeledStmt(ls) ==
  IF \E l \in Any, st: ls = [label |-> l, stmt |-> st]
  THEN
    CHOOSE l, st:
      ls = [label |-> l, stmt |-> st] /\ TRUE
    IN << l, ":" >> \o EmitStmt(st)
  ELSE <<"/* MalformedLabeledStmt */">>

EmitStmtSeq(ss) ==
  IF ss \in Seq(Any) THEN
    IF Len(ss) = 0 THEN << >>
    ELSE EmitLabeledStmt(ss[1]) \o EmitStmtSeq(SubSeq(ss, 2, Len(ss)))
  ELSE <<"/* MalformedStmtSeq */">>

EmitProcedure(pr) ==
  IF IsProcedure(pr) THEN
    CHOOSE n \in Any, ps \in Seq(Any), b:
      pr = [tag |-> "Procedure", name |-> n, params |-> ps, body |-> b]
    IN <<"procedure", n, "(",>>
       \o JoinWith(",", ps)
       \o <<")", "==">>
       \o EmitStmtSeq(b)
  ELSE <<"/* MalformedProcedure */">>

EmitProcess(pc) ==
  IF IsProcess(pc) THEN
    CHOOSE n \in Any, self \in Any, f \in {"None","WF","SF"}, b:
      pc = [tag |-> "Process", name |-> n, self |-> self, fairness |-> f, body |-> b]
    IN <<"process", n, "(", self, ")", "fair", f, "{" >>
       \o EmitStmtSeq(b) \o <<"}">>
  ELSE <<"/* MalformedProcess */">>

(***************************************************************************)
(* Top-level emission: Init, Next, Spec, Termination                       *)
(***************************************************************************)

(*
EmitInit/EmitNext are placeholders that would normally encode initial-state
and step-relation expansions from the AST. We emit simple stubs while the
Spec/Termination composition reflects fairness choices.
*)

EmitInit(a) ==
  <<"Init", "==", "TRUE">>

EmitNext(a) ==
  <<"Next", "==", "UNCHANGED", "vars">>

EmitSpec(a) ==
  IF \E nm \in Any, vs \in Seq(Any), pcs \in Seq(Any), ps \in Seq(Any), f \in {"NoFairness","WFProc","WFNext","SFProc"}:
       a = [tag |-> "Algorithm", name |-> nm, vars |-> vs, procedures |-> pcs, processes |-> ps, fairness |-> f]
  THEN
    CHOOSE nm \in Any, vs \in Seq(Any), pcs \in Seq(Any), ps \in Seq(Any), f \in {"NoFairness","WFProc","WFNext","SFProc"}:
      a = [tag |-> "Algorithm", name |-> nm, vars |-> vs, procedures |-> pcs, processes |-> ps, fairness |-> f]
    IN CASE f = "NoFairness" ->
           <<"Spec", "==", "Init", "/\\", "[][Next]_vars">>
       [] f = "WFProc"   ->
           <<"Spec", "==", "Init", "/\\", "[][Next]_vars",
             "/\\", "\\A p \\in ProcIds :", "WF_vars(ProcNext(p))">>
       [] f = "WFNext"   ->
           <<"Spec", "==", "Init", "/\\", "WF_vars(Next)">>
       [] f = "SFProc"   ->
           <<"Spec", "==", "Init", "/\\", "[][Next]_vars",
             "/\\", "\\A p \\in ProcIds :", "SF_vars(ProcNext(p))">>
       [] OTHER ->
           <<"Spec", "==", "Init", "/\\", "[][Next]_vars">>
  ELSE
    <<"Spec", "==", "Init", "/\\", "[][Next]_vars">>

EmitTermination(a) ==
  <<"Termination", "==", "<>[]", "Done">>

EmitAlgorithm(a) ==
  IF IsAlgorithm(a) THEN
    CHOOSE nm \in Any, vs \in Seq(Any), pcs \in Seq(Any), ps \in Seq(Any), f \in {"NoFairness","WFProc","WFNext","SFProc"}:
      a = [tag |-> "Algorithm", name |-> nm, vars |-> vs, procedures |-> pcs, processes |-> ps, fairness |-> f]
    IN [ Header      |-> <<"----", "MODULE", nm, "----">>,
         Variables   |-> <<"VARIABLES">> \o JoinWith(",", vs),
         Procedures  |-> IF Len(pcs) = 0 THEN << >> ELSE
                           \* concatenate emitted procedures
                           IF Len(pcs) = 1 THEN EmitProcedure(pcs[1])
                           ELSE EmitProcedure(pcs[1]) \o <<"\n">> \o
                                EmitAlgorithm([tag |-> "Algorithm", name |-> nm,
                                               vars |-> vs, procedures |-> SubSeq(pcs, 2, Len(pcs)),
                                               processes |-> ps, fairness |-> f]).Procedures,
         Processes   |-> IF Len(ps) = 0 THEN << >> ELSE
                           IF Len(ps) = 1 THEN EmitProcess(ps[1])
                           ELSE EmitProcess(ps[1]) \o <<"\n">> \o
                                EmitAlgorithm([tag |-> "Algorithm", name |-> nm,
                                               vars |-> vs, procedures |-> pcs,
                                               processes |-> SubSeq(ps, 2, Len(ps)),
                                               fairness |-> f]).Processes,
         Init        |-> EmitInit(a),
         Next        |-> EmitNext(a),
         Spec        |-> EmitSpec(a),
         Termination |-> EmitTermination(a),
         Footer      |-> <<"====