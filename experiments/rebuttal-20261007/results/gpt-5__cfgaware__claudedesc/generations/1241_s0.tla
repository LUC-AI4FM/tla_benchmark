---- MODULE OldPlusCal ----
EXTENDS Naturals, Sequences, TLC

(*
  OldPlusCal is a utility/specification module that formalizes a simplified,
  partially executable translation from a +CAL algorithm's abstract syntax tree
  (AST) to a TLA+ description represented as a sequence of lexemes (strings).

  This module is not a model of a running system. It specifies the structure of
  +CAL ASTs via predicates and set-forming operators and provides a functional
  Translation(alg, fairnessOption) that returns a sequence of lexemes.
*)

CONSTANTS
  ast,        \* externally supplied +CAL AST
  fairness,   \* externally supplied fairness option: "", "wf", "wfNext", or "sf"
  Object,     \* provided by the external configuration
  Any         \* provided by the external configuration

(***************************************************************************)
(* AST Grammar Predicates and Sets                                         *)
(***************************************************************************)

FairnessOptions == {"", "wf", "wfNext", "sf"}

IsFairnessOption(f) == f \in FairnessOptions

IsStringSeq(x) == \* A very weak check that x is a sequence of lexemes (strings)
  /\ x \in Seq(STRING)

IsVarName(x) == x \in STRING

IsExpr(e) == IsStringSeq(e)

IsVarDecl(d) ==
  \/ d \in STRING
  \/ (/\ "tag" \in DOMAIN d /\ d.tag = "VarDecl"
      /\ "name" \in DOMAIN d /\ IsVarName(d.name)
      /\ ~("init" \in DOMAIN d) \/ IsExpr(d.init))

IsProc(p) ==
  /\ "tag" \in DOMAIN p /\ p.tag = "Procedure"
  /\ "name" \in DOMAIN p /\ p.name \in STRING
  /\ "params" \in DOMAIN p /\ p.params \in Seq(STRING)
  /\ "locals" \in DOMAIN p /\ p.locals \in Seq(STRING)
  /\ "body" \in DOMAIN p /\ IsLabelSeq(p.body)

IsProcess(P) ==
  /\ "tag" \in DOMAIN P /\ P.tag = "Process"
  /\ "name" \in DOMAIN P /\ P.name \in STRING
  /\ "domain" \in DOMAIN P /\ IsExpr(P.domain)
  /\ "locals" \in DOMAIN P /\ P.locals \in Seq(STRING)
  /\ "body" \in DOMAIN P /\ IsLabelSeq(P.body)

IsAlgorithm(alg) ==
  /\ "tag" \in DOMAIN alg /\ alg.tag = "Algorithm"
  /\ "name" \in DOMAIN alg /\ alg.name \in STRING
  /\ "procs" \in DOMAIN alg /\ alg.procs \in Seq({})
  /\ \A pr \in SeqToSet(alg.procs): IsProc(pr)
  /\ "vars" \in DOMAIN alg /\ alg.vars \in Seq({})
  /\ \A vd \in SeqToSet(alg.vars): IsVarDecl(vd)
  /\ "processes" \in DOMAIN alg /\ alg.processes \in Seq({})
  /\ \A P \in SeqToSet(alg.processes): IsProcess(P)
  /\ "body" \in DOMAIN alg /\ IsLabelSeq(alg.body)

IsUniProcessAlgorithm(alg) ==
  IsAlgorithm(alg) /\ Len(alg.processes) = 0

IsMultiProcessAlgorithm(alg) ==
  IsAlgorithm(alg) /\ Len(alg.processes) > 0

(***************************************************************************)
(* Labeled/Compound Statements                                             *)
(***************************************************************************)

IsLabeled(s) ==
  /\ "tag" \in DOMAIN s /\ s.tag = "Labeled"
  /\ "label" \in DOMAIN s /\ s.label \in STRING
  /\ "stmt" \in DOMAIN s /\ IsStmt(s.stmt)

IsWhile(s) ==
  /\ "tag" \in DOMAIN s /\ s.tag = "While"
  /\ "cond" \in DOMAIN s /\ IsExpr(s.cond)
  /\ "body" \in DOMAIN s /\ IsLabelSeq(s.body)

IsLabelSeq(S) ==
  /\ S \in Seq({})
  /\ \A x \in SeqToSet(S): IsLabeled(x) \/ IsWhile(x) \/ IsLabelSeq(x) \/ IsSimple(x)

(***************************************************************************)
(* Simple Statements                                                       *)
(***************************************************************************)

IsAssign(s) ==
  /\ "tag" \in DOMAIN s /\ s.tag = "Assign"
  /\ "lhs" \in DOMAIN s /\ IsExpr(s.lhs)
  /\ "rhs" \in DOMAIN s /\ IsExpr(s.rhs)

IsIf(s) ==
  /\ "tag" \in DOMAIN s /\ s.tag = "If"
  /\ "guards" \in DOMAIN s /\ s.guards \in Seq({})
  /\ \A g \in SeqToSet(s.guards): /\ "cond" \in DOMAIN g /\ IsExpr(g.cond)
                                  /\ "body" \in DOMAIN g /\ IsLabelSeq(g.body)

IsEither(s) ==
  /\ "tag" \in DOMAIN s /\ s.tag = "Either"
  /\ "branches" \in DOMAIN s /\ s.branches \in Seq({})
  /\ \A b \in SeqToSet(s.branches): IsLabelSeq(b)

IsWith(s) ==
  /\ "tag" \in DOMAIN s /\ s.tag = "With"
  /\ "quant" \in DOMAIN s /\ IsExpr(s.quant)
  /\ "body" \in DOMAIN s /\ IsLabelSeq(s.body)

IsWhen(s) ==
  /\ "tag" \in DOMAIN s /\ s.tag = "When"
  /\ "cond" \in DOMAIN s /\ IsExpr(s.cond)

IsPrint(s) ==
  /\ "tag" \in DOMAIN s /\ s.tag = "Print"
  /\ "expr" \in DOMAIN s /\ IsExpr(s.expr)

IsAssert(s) ==
  /\ "tag" \in DOMAIN s /\ s.tag = "Assert"
  /\ "expr" \in DOMAIN s /\ IsExpr(s.expr)

IsSkip(s) ==
  /\ "tag" \in DOMAIN s /\ s.tag = "Skip"

IsCall(s) ==
  /\ "tag" \in DOMAIN s /\ s.tag = "Call"
  /\ "proc" \in DOMAIN s /\ s.proc \in STRING
  /\ "args" \in DOMAIN s /\ s.args \in Seq(STRING)

IsReturn(s) ==
  /\ "tag" \in DOMAIN s /\ s.tag = "Return"

IsCallReturn(s) ==
  /\ "tag" \in DOMAIN s /\ s.tag = "CallReturn"
  /\ "proc" \in DOMAIN s /\ s.proc \in STRING
  /\ "args" \in DOMAIN s /\ s.args \in Seq(STRING)

IsGoto(s) ==
  /\ "tag" \in DOMAIN s /\ s.tag = "Goto"
  /\ "label" \in DOMAIN s /\ s.label \in STRING

IsSimple(s) ==
  IsAssign(s) \/ IsIf(s) \/ IsEither(s) \/ IsWith(s) \/ IsWhen(s) \/
  IsPrint(s) \/ IsAssert(s) \/ IsSkip(s) \/ IsCall(s) \/ IsReturn(s) \/
  IsCallReturn(s) \/ IsGoto(s)

IsStmt(s) == IsSimple(s) \/ IsWhile(s) \/ IsLabelSeq(s)

(***************************************************************************)
(* Utilities on Sequences of Lexemes                                       *)
(***************************************************************************)

RECURSIVE FlattenLexemes(_)
FlattenLexemes(ss) ==
  IF ss \in Seq(Seq(STRING)) THEN
    IF Len(ss) = 0 THEN <<>>
    ELSE Head(ss) \o FlattenLexemes(Tail(ss))
  ELSE
    <<>>

Lex(x) == <<x>> \* pack one lexeme

SepBy(ss, sep) == \* concatenate a sequence of sequences inserting sep as a single lexeme
  IF Len(ss) = 0 THEN <<>>
  ELSE IF Len(ss) = 1 THEN Head(ss)
  ELSE Head(ss) \o Lex(sep) \o SepBy(Tail(ss), sep)

(***************************************************************************)
(* Explosion of labeled statements into atomic actions                      *)
(***************************************************************************)

RECURSIVE FullyExplodeSeq(_)
FullyExplodeSeq(S) ==
  IF Len(S) = 0 THEN <<>>
  ELSE Explode(Head(S)) \o FullyExplodeSeq(Tail(S))

RECURSIVE Explode(_)
Explode(s) ==
  IF IsLabelSeq(s) THEN FullyExplodeSeq(s)
  ELSE IF IsWhile(s) THEN
    \* Replace while with a canonical labeled test and body, as a flat approximation
    LET testLbl == [tag |-> "Labeled", label |-> "whileTest", stmt |-> [tag |-> "When", cond |-> <<"(", "not", ")", "implemented">>]]
        bodyLbls == s.body
    IN FullyExplodeSeq(<< testLbl >> \o bodyLbls)
  ELSE IF IsLabeled(s) THEN << s >>
  ELSE IF IsStmt(s) THEN << s >>
  ELSE << s >>

(***************************************************************************)
(* Collect bodies for algorithms                                            *)
(***************************************************************************)

AlgAllLabeled(alg) ==
  IF IsMultiProcessAlgorithm(alg) THEN
    \* concatenate all processes' bodies
    LET ps == alg.processes IN
      [ i \in 1..Len(ps) |-> ps[i].body ][i \in 1..Len(ps)] \o <<>> \* dummy
    \* Above trick isn't directly usable for concatenation; build with recursion
  ELSE
    alg.body

RECURSIVE ConcatBodies(_)
ConcatBodies(ps) ==
  IF Len(ps) = 0 THEN <<>>
  ELSE
    LET p == Head(ps)
    IN p.body \o ConcatBodies(Tail(ps))

BodiesOf(alg) ==
  IF IsMultiProcessAlgorithm(alg) THEN ConcatBodies(alg.processes) ELSE alg.body

(***************************************************************************)
(* Translation core                                                         *)
(***************************************************************************)

FairnessTokens(f) ==
  CASE f = "" -> <<>>
     [] f = "wf" \/ f = "wfNext" -> <<"/\\", "WF_vars(Next)">>
     [] f = "sf" -> <<"/\\", "SF_vars(Next)">>
     [] OTHER -> <<>>

TokenizeVarDecl(vd) ==
  IF vd \in STRING THEN <<vd>>
  ELSE IF "name" \in DOMAIN vd THEN <<vd.name>>
  ELSE <<"var">>

VarsLineTokens(alg) ==
  \* Always include pc and stack; user vars are abstracted to a single placeholder for simplicity.
  <<"VARIABLES", "pc", ",", "stack", ",", "userVars">>

ProcSetTokens(alg) ==
  IF IsMultiProcessAlgorithm(alg) THEN
    IF Len(alg.processes) >= 1 THEN
      LET p1 == alg.processes[1] IN <<"ProcSet", "==">> \o p1.domain
    ELSE <<"ProcSet", "==", "{ }">>
  ELSE
    <<"ProcSet", "==", "{", "self", "}">>

HeaderTokens(alg) ==
  LET nm == IF "name" \in DOMAIN alg THEN alg.name ELSE "Unnamed"
  IN <<"----", "MODULE", nm, "----">>

FooterTokens == <<"====