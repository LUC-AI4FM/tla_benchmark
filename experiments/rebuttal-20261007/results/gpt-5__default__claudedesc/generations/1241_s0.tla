------------------------------ MODULE OldPlusCal ------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

(*
  OldPlusCal formalizes a simplified, partially-executable translation from a +CAL AST
  to a TLA+ specification as a sequence of string lexemes.
*)

CONSTANTS ast, fairness

VARIABLES out

(***************************************************************************)
(* Basic lexical domains                                                   *)
(***************************************************************************)

Lexeme == STRING
Expr == Seq(Lexeme)
Name == STRING
Label == STRING

StatementKinds ==
  {"Assign","If","Either","With","When","Print","Assert","Skip",
   "While","Call","Return","CallReturn","Goto"}

(***************************************************************************)
(* AST shape predicates (lightweight/structural)                           *)
(***************************************************************************)

(*
  Statements are represented as records with a "kind" field drawn from StatementKinds
  and other fields as appropriate to the kind.
*)

IsAssign(st) ==
  /\ DOMAIN st = {"kind","pairs"}
  /\ st.kind = "Assign"
  /\ st.pairs \in Seq([lhs: Expr, rhs: Expr])

IsIf(st) ==
  /\ DOMAIN st = {"kind","branches","else"}
  /\ st.kind = "If"
  /\ st.branches \in Seq([cond: Expr, then: Seq(STRING)]) \* body encoded via labels; relaxed check
  /\ st.else \in Seq(STRING) \/ st.else = <<>>

IsEither(st) ==
  /\ DOMAIN st = {"kind","branches"}
  /\ st.kind = "Either"
  /\ st.branches \in Seq(Seq(STRING))

IsWith(st) ==
  /\ DOMAIN st = {"kind","bounds","body"}
  /\ st.kind = "With"
  /\ st.bounds \in Seq([name: Name, domain: Expr])
  /\ st.body \in Seq(STRING)

IsWhen(st) ==
  /\ DOMAIN st = {"kind","cond"}
  /\ st.kind = "When"
  /\ st.cond \in Expr

IsPrint(st) ==
  /\ DOMAIN st = {"kind","expr"}
  /\ st.kind = "Print"
  /\ st.expr \in Expr

IsAssert(st) ==
  /\ DOMAIN st = {"kind","expr","msg"}
  /\ st.kind = "Assert"
  /\ st.expr \in Expr
  /\ st.msg \in STRING

IsSkip(st) ==
  /\ DOMAIN st = {"kind"}
  /\ st.kind = "Skip"

IsWhile(st) ==
  /\ DOMAIN st = {"kind","cond","body"}
  /\ st.kind = "While"
  /\ st.cond \in Expr
  /\ st.body \in Seq(STRING)

IsCall(st) ==
  /\ DOMAIN st = {"kind","proc","args"}
  /\ st.kind = "Call"
  /\ st.proc \in Name
  /\ st.args \in Seq(Expr)

IsReturn(st) ==
  /\ DOMAIN st = {"kind"}
  /\ st.kind = "Return"

IsCallReturn(st) ==
  /\ DOMAIN st = {"kind","proc","args"}
  /\ st.kind = "CallReturn"
  /\ st.proc \in Name
  /\ st.args \in Seq(Expr)

IsGoto(st) ==
  /\ DOMAIN st = {"kind","target"}
  /\ st.kind = "Goto"
  /\ st.target \in Label

IsStatement(st) ==
  IsAssign(st) \/ IsIf(st) \/ IsEither(st) \/ IsWith(st) \/ IsWhen(st) \/
  IsPrint(st) \/ IsAssert(st) \/ IsSkip(st) \/ IsWhile(st) \/
  IsCall(st) \/ IsReturn(st) \/ IsCallReturn(st) \/ IsGoto(st)

(*
  Labeled statements and sequences thereof
*)
IsLabeledStmt(ls) ==
  /\ DOMAIN ls = {"kind","label","stmt"}
  /\ ls.kind = "Labeled"
  /\ ls.label \in Label
  /\ ls.stmt \in [kind: STRING]  \* relaxed: avoid deep inspection by default

RECURSIVE IsLabelSeq(_)
IsLabelSeq(s) ==
  IF Len(s) = 0 THEN TRUE
  ELSE /\ IsLabeledStmt(s[1])
       /\ IsLabelSeq(IF Len(s) = 1 THEN <<>> ELSE SubSeq(s,2,Len(s)))

(*
  Procedure and process shapes
*)
IsProcedure(p) ==
  /\ DOMAIN p = {"kind","name","params","locals","body"}
  /\ p.kind = "Proc"
  /\ p.name \in Name
  /\ p.params \in Seq(Name)
  /\ p.locals \in Seq(Name)
  /\ p.body \in Seq(STRING)

IsProcess(pr) ==
  /\ DOMAIN pr = {"kind","name","idParam","locals","procsetExpr","body"}
  /\ pr.kind = "Process"
  /\ pr.name \in Name
  /\ pr.idParam \in Name
  /\ pr.locals \in Seq(Name)
  /\ pr.procsetExpr \in Expr
  /\ pr.body \in Seq(STRING)

(*
  Algorithms: uniprocess and multiprocess
*)
IsUniAlgorithm(alg) ==
  /\ DOMAIN alg = {"kind","name","variables","procedures","body"}
  /\ alg.kind = "UniAlg"
  /\ alg.name \in Name
  /\ alg.variables \in Seq(Name)
  /\ alg.procedures \in Seq([kind: STRING]) \* relaxed
  /\ alg.body \in Seq(STRING)

IsMultiAlgorithm(alg) ==
  /\ DOMAIN alg = {"kind","name","variables","procedures","processes"}
  /\ alg.kind = "MultiAlg"
  /\ alg.name \in Name
  /\ alg.variables \in Seq(Name)
  /\ alg.procedures \in Seq([kind: STRING]) \* relaxed
  /\ alg.processes \in Seq([kind: STRING]) \* relaxed

IsAlgorithm(alg) == IsUniAlgorithm(alg) \/ IsMultiAlgorithm(alg)

(***************************************************************************)
(* Sequence utilities                                                      *)
(***************************************************************************)

Head(s) == s[1]
Tail(s) == IF Len(s) = 0 THEN <<>> ELSE IF Len(s) = 1 THEN <<>> ELSE SubSeq(s,2,Len(s))

RECURSIVE Flatten(_)
Flatten(ss) ==
  IF Len(ss) = 0 THEN <<>>
  ELSE Head(ss) \o Flatten(Tail(ss))

RECURSIVE Intercalate(_,_)
Intercalate(ss, sep) ==
  IF Len(ss) = 0 THEN <<>>
  ELSE IF Len(ss) = 1 THEN Head(ss)
  ELSE Head(ss) \o sep \o Intercalate(Tail(ss), sep)

RECURSIVE NamesToTokenGroups(_)
NamesToTokenGroups(ns) ==
  IF Len(ns) = 0 THEN <<>>
  ELSE << << ns[1] >> >> \o NamesToTokenGroups(IF Len(ns) = 1 THEN <<>> ELSE SubSeq(ns,2,Len(ns)))

RECURSIVE MapLocals(_,_)
MapLocals(ns, id) ==
  IF Len(ns) = 0 THEN <<>>
  ELSE << << ns[1], "[", id, "]" >> >> \o MapLocals(IF Len(ns) = 1 THEN <<>> ELSE SubSeq(ns,2,Len(ns)), id)

RECURSIVE ProcLocalGroups(_)
ProcLocalGroups(procs) ==
  IF Len(procs) = 0 THEN <<>>
  ELSE
    LET p == Head(procs) IN
      MapLocals(p.locals, p.idParam) \o ProcLocalGroups(Tail(procs))

(***************************************************************************)
(* Explosion of labeled statements to atomic action tokens                 *)
(***************************************************************************)

Explode(lblStmt) ==
  LET l == lblStmt.label
      k == lblStmt.stmt.kind
  IN
  << "ACTION", l, "==", "(*", "exploded", "atomic", "step:", k, "from", l, "*)" >>

RECURSIVE FullyExplodeSeq(_)
FullyExplodeSeq(labelSeq) ==
  IF Len(labelSeq) = 0 THEN <<>>
  ELSE Explode(Head(labelSeq)) \o FullyExplodeSeq(Tail(labelSeq))

RECURSIVE ExplodeProcedures(_)
ExplodeProcedures(procs) ==
  IF Len(procs) = 0 THEN <<>>
  ELSE
    LET p == Head(procs) IN
      << "(*", "procedure", p.name, "*)" >> \o
      FullyExplodeSeq(p.body) \o
      ExplodeProcedures(Tail(procs))

RECURSIVE ExplodeProcesses(_)
ExplodeProcesses(procs) ==
  IF Len(procs) = 0 THEN <<>>
  ELSE
    LET pr == Head(procs) IN
      << "(*", "process", pr.name, "*)" >> \o
      FullyExplodeSeq(pr.body) \o
      ExplodeProcesses(Tail(procs))

(***************************************************************************)
(* Translation helpers                                                     *)
(***************************************************************************)

ComposeVarGroups(alg) ==
  LET globals == NamesToTokenGroups(alg.variables)
      locals ==
        IF alg.kind = "MultiAlg"
        THEN ProcLocalGroups(alg.processes)
        ELSE <<>>
  IN globals \o locals

VariablesSectionTokens(alg) ==
  LET varGroups == << << "pc" >>, << "stack" >> >> \o ComposeVarGroups(alg)
  IN << "VARIABLES" >> \o Intercalate(varGroups, << ",">>)

VarsDefinitionTokens(alg) ==
  LET varGroups == << << "pc" >>, << "stack" >> >> \o ComposeVarGroups(alg)
  IN << "vars", "==", "<<">> \o Intercalate(varGroups, << ",">>) \o << ">>" >>

ProcSetTokens(alg) ==
  IF alg.kind = "MultiAlg"
  THEN << "ProcSet", "==">> \o Head(<< alg.processes[1].procsetExpr >>) \* first proc's procsetExpr as representative
  ELSE << "ProcSet", "==", "{}" >>

InitTokens(alg) ==
  << "Init", "==",
     "(*", "generated", "Init:", "pc", "and", "stack", "initialized", "*)" >>

NextTokens(alg) ==
  << "Next", "==",
     "(*", "generated", "Next:", "pc'", "and", "stack'", "updated", "*)" >>

TerminationTokens(alg) ==
  IF alg.kind = "MultiAlg"
  THEN << "Termination", "==", "(*", "pc[self]", "=", "Done", "*)" >>
  ELSE << "Termination", "==", "(*", "pc", "=", "Done", "*)" >>

FairnessTokens(f) ==
  CASE f = "wf" -> << "/\\", "WF_vars(Next)" >>
    [] f = "wfNext" -> << "/\\", "WF_vars(Next)" >>
    [] f = "sf" -> << "/\\", "SF_vars(Next)" >>
    [] OTHER -> <<>>

SpecTokens(alg, f) ==
  << "Spec", "==", "Init", "/\\", "[][Next]_vars" >> \o FairnessTokens(f)

HeaderTokens(alg) ==
  << "----", "MODULE", alg.name, "----" >>

ExtendsTokens ==
  << "EXTENDS", "Naturals", ",", "Sequences", ",", "FiniteSets", ",", "TLC" >>

FooterTokens == << "====