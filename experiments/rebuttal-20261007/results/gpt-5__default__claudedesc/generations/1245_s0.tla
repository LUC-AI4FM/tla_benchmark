---------------------------- MODULE XPlusCal ----------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS
  AST, \* An externally supplied +CAL Algorithm AST
  Fairness \* One of {"", "wf", "wfNext", "sf"}

(***************************************************************************)
(* Basic lexical/domain definitions                                         *)
(***************************************************************************)

Lexeme == STRING
Expr(e) == /\ IsSeq(e) /\ \A i \in DOMAIN e: e[i] \in Lexeme

IsSeq(s) == \E n \in Nat: DOMAIN s = 1..n
AllStrings(s) == Expr(s)

FairnessOptions == {"", "wf", "wfNext", "sf"}

StmtTags == {
  "While", "LabelSeq", "LabelIf", "LabelEither",
  "Final", "Assign", "CallOrReturn", "Goto", "Simple"
}

(***************************************************************************)
(* Mutually recursive grammar predicates for +CAL ASTs                      *)
(***************************************************************************)

RECURSIVE IsLabeledStmt(_)

IsVarDecl(d) ==
  /\ {"tag","name","init"} \subseteq DOMAIN d
  /\ d.tag = "VarDecl"
  /\ d.name \in STRING
  /\ AllStrings(d.init)

IsPVarDecl(d) ==
  /\ {"tag","name","init"} \subseteq DOMAIN d
  /\ d.tag = "PVarDecl"
  /\ d.name \in STRING
  /\ AllStrings(d.init)

IsSimpleStmt(s) ==
  /\ {"tag","text"} \subseteq DOMAIN s
  /\ s.tag = "Simple"
  /\ AllStrings(s.text)

IsFinalStmt(s) ==
  /\ {"tag","inner"} \subseteq DOMAIN s
  /\ s.tag = "Final"
  /\ IsSimpleStmt(s.inner)

IsAssign(s) ==
  /\ {"tag","lhs","rhs"} \subseteq DOMAIN s
  /\ s.tag = "Assign"
  /\ IsSeq(s.lhs) /\ \A i \in DOMAIN s.lhs: Expr(s.lhs[i])
  /\ IsSeq(s.rhs) /\ \A i \in DOMAIN s.rhs: Expr(s.rhs[i])

IsCallOrReturn(s) ==
  /\ {"tag","kind","proc","args"} \subseteq DOMAIN s
  /\ s.tag = "CallOrReturn"
  /\ s.kind \in {"call","return"}
  /\ s.proc \in STRING
  /\ IsSeq(s.args) /\ \A i \in DOMAIN s.args: Expr(s.args[i])

IsGoto(s) ==
  /\ {"tag","target"} \subseteq DOMAIN s
  /\ s.tag = "Goto"
  /\ s.target \in STRING

IsWhile(s) ==
  /\ {"tag","cond","body"} \subseteq DOMAIN s
  /\ s.tag = "While"
  /\ AllStrings(s.cond)
  /\ IsLabeledStmt(s.body)

IsLabelSeq(s) ==
  /\ {"tag","seq"} \subseteq DOMAIN s
  /\ s.tag = "LabelSeq"
  /\ IsSeq(s.seq) /\ \A i \in DOMAIN s.seq: IsLabeledStmt(s.seq[i])

IsLabelIf(s) ==
  /\ {"tag","guards","thens","else"} \subseteq DOMAIN s
  /\ s.tag = "LabelIf"
  /\ IsSeq(s.guards) /\ \A i \in DOMAIN s.guards: Expr(s.guards[i])
  /\ IsSeq(s.thens) /\ \A i \in DOMAIN s.thens: IsLabeledStmt(s.thens[i])
  /\ IsLabeledStmt(s.else)

IsLabelEither(s) ==
  /\ {"tag","arms"} \subseteq DOMAIN s
  /\ s.tag = "LabelEither"
  /\ IsSeq(s.arms) /\ \A i \in DOMAIN s.arms: IsLabeledStmt(s.arms[i])

IsLabeledStmt(s) ==
  /\ {"labels","tag"} \subseteq DOMAIN s
  /\ IsSeq(s.labels) /\ \A i \in DOMAIN s.labels: s.labels[i] \in STRING
  /\ s.tag \in StmtTags
  /\ CASE s.tag = "While"       -> IsWhile(s)
       [] s.tag = "LabelSeq"    -> IsLabelSeq(s)
       [] s.tag = "LabelIf"     -> IsLabelIf(s)
       [] s.tag = "LabelEither" -> IsLabelEither(s)
       [] s.tag = "Final"       -> IsFinalStmt(s)
       [] s.tag = "Assign"      -> IsAssign(s)
       [] s.tag = "CallOrReturn"-> IsCallOrReturn(s)
       [] s.tag = "Goto"        -> IsGoto(s)
       [] s.tag = "Simple"      -> IsSimpleStmt(s)

IsProcedure(p) ==
  /\ {"tag","name","params","body"} \subseteq DOMAIN p
  /\ p.tag = "Procedure"
  /\ p.name \in STRING
  /\ IsSeq(p.params) /\ \A i \in DOMAIN p.params: p.params[i] \in STRING
  /\ IsLabeledStmt(p.body)

IsProcess(pr) ==
  /\ {"tag","name","locals","body"} \subseteq DOMAIN pr
  /\ pr.tag = "Process"
  /\ pr.name \in STRING
  /\ IsSeq(pr.locals) /\ \A i \in DOMAIN pr.locals: IsVarDecl(pr.locals[i])
  /\ IsLabeledStmt(pr.body)

IsAlgorithm(a) ==
  /\ {"tag","kind","name","body"} \subseteq DOMAIN a
  /\ a.tag = "Algorithm"
  /\ a.kind \in {"uni","multi"}
  /\ a.name \in STRING
  /\ IsLabeledStmt(a.body)

(***************************************************************************)
(* Structural utilities                                                     *)
(***************************************************************************)

RECURSIVE ConcatSeqs(_)
ConcatSeqs(ss) ==
  IF Len(ss) = 0 THEN << >> ELSE Head(ss) \o ConcatSeqs(Tail(ss))

RECURSIVE Explode(_)
Explode(s) ==
  \* Explode labeled statements into a flat sequence of simple labeled statements.
  \* This simplified version only flattens LabelSeq; other forms are left as singletons.
  IF s.tag = "LabelSeq" THEN
    ConcatSeqs([ i \in 1..Len(s.seq) |-> Explode(s.seq[i]) ])
  ELSE
    << s >>

FullyExplodeSeq(S) ==
  ConcatSeqs([ i \in 1..Len(S) |-> Explode(S[i]) ])

XlateCall(S) == S
XlateReturn(S) == S
XlateCallReturn(S) == S
XlateGoto(S) == S

XlatePipeline(S) == XlateGoto(XlateCallReturn(XlateReturn(XlateCall(S))))

AddSubscript(S, pcVar) == S

ProcessVars(a) == {} \* Placeholder for computed process-local variables

Assemble(a, S, fairness) ==
  LET
    header ==
      << "----", "MODULE", a.name, "----" >>
    extends ==
      << "EXTENDS", "Naturals", "Sequences", "TLC" >>
    initText ==
      << "Init", "==", "(*", "generated", "initializer", "*)" >>
    nextText ==
      << "Next", "==", "(*", "generated", "next-state", "action", "*)" >>
    specCore ==
      << "Spec", "==", "Init", "/\\", "[]", "[", "Next", "]", "_", "<<", "vars", ">>" >>
    fairnessText ==
      IF fairness = "" THEN
        << >>
      ELSE IF fairness = "wf" THEN
        << "/\\", "WF_", "<<", "vars", ">>", "(", "Next", ")" >>
      ELSE IF fairness = "wfNext" THEN
        << "/\\", "WF_", "<<", "vars", ">>", "(", "Next", ")" >>
      ELSE IF fairness = "sf" THEN
        << "/\\", "SF_", "<<", "vars", ">>", "(", "Next", ")" >>
      ELSE << >>
    termText ==
      << "Termination", "==", "<>", "Terminated" >>
    footer ==
      << "====