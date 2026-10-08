------------------------------ MODULE XPlusCal ------------------------------

EXTENDS Sequences, TLC, Naturals

(*
  This module sketches a translator-specification for +CAL ASTs to TLA+,
  following the high-level description of XPlusCal. It represents TLA+
  expressions as sequences of string lexemes and provides mutually
  recursive predicates for the principal AST categories.

  The core operator Translation(alg, fairnessOption) returns a sequence
  of lexemes intended to be the TLA+ specification text for the given
  +CAL algorithm AST and fairness choice in {"", "wf", "wfNext", "sf"}.

  The constants Object and Any are intended to be bound by the model
  configuration to an AST and a fairness option, respectively.
*)

CONSTANTS
  Object, \* externally supplied AST
  Any     \* externally supplied fairness option

(****************************************************************)
(* Basic lexeme and expression representation                    *)
(****************************************************************)

Lexeme == STRING
LexSeq == Seq(STRING)

IsLexSeq(s) == IsSeq(s) /\ \A i \in DOMAIN s: s[i] \in STRING
IsExpr(e) == IsLexSeq(e)

(****************************************************************)
(* Mutually recursive AST shape predicates                       *)
(****************************************************************)

RECURSIVE
  IsAlgorithm(_),
  IsProcedure(_),
  IsProcess(_),
  IsVarDecl(_),
  IsPVarDecl(_),
  IsLabeledStmt(_),
  IsWhile(_),
  IsLabelSeq(_),
  IsLabelIf(_),
  IsLabelEither(_),
  IsFinalStmt(_),
  IsAssign(_),
  IsCallOrReturn(_),
  IsGoto(_),
  IsSimpleStmt(_)

IsVarDecl(d) ==
  /\ d.type = "VarDecl"
  /\ IsSeq(d.names) /\ \A i \in DOMAIN d.names: d.names[i] \in STRING
  /\ IsSeq(d.inits) /\ \A i \in DOMAIN d.inits: IsExpr(d.inits[i])

IsPVarDecl(d) ==
  /\ d.type = "PVarDecl"
  /\ IsSeq(d.names) /\ \A i \in DOMAIN d.names: d.names[i] \in STRING
  /\ IsSeq(d.inits) /\ \A i \in DOMAIN d.inits: IsExpr(d.inits[i])

IsSimpleStmt(s) ==
  /\ s.type \in {"Skip","Assert","Print","Stmt"}
  /\ (s.type \in {"Assert","Stmt"} => IsExpr(s.expr))
  /\ (s.type = "Print" => IsExpr(s.args))

IsAssign(a) ==
  /\ a.type = "Assign"
  /\ IsSeq(a.lhs) /\ \A i \in DOMAIN a.lhs: a.lhs[i] \in STRING
  /\ IsSeq(a.rhs) /\ \A i \in DOMAIN a.rhs: IsExpr(a.rhs[i])

IsCallOrReturn(c) ==
  /\ c.type \in {"Call","Return","CallReturn"}
  /\ (c.type = "Call" => c.proc \in STRING /\ IsSeq(c.args) /\ \A i \in DOMAIN c.args: IsExpr(c.args[i]))
  /\ (c.type = "Return" => TRUE)
  /\ (c.type = "CallReturn" => c.proc \in STRING /\ IsSeq(c.args) /\ \A i \in DOMAIN c.args: IsExpr(c.args[i]))

IsGoto(g) ==
  /\ g.type = "Goto"
  /\ g.target \in STRING

IsFinalStmt(f) ==
  /\ f.type = "Final"

IsWhile(w) ==
  /\ w.type = "While"
  /\ IsExpr(w.cond)
  /\ IsLabelSeq(w.body)

IsLabelIf(ifr) ==
  /\ ifr.type = "If"
  /\ IsSeq(ifr.guards) /\ \A i \in DOMAIN ifr.guards: IsExpr(ifr.guards[i])
  /\ IsSeq(ifr.blocks) /\ \A i \in DOMAIN ifr.blocks: IsLabelSeq(ifr.blocks[i])
  /\ Len(ifr.guards) = Len(ifr.blocks)

IsLabelEither(e) ==
  /\ e.type = "Either"
  /\ IsSeq(e.blocks) /\ \A i \in DOMAIN e.blocks: IsLabelSeq(e.blocks[i])

IsLabeledStmt(ls) ==
  /\ ls.type = "Labeled"
  /\ ls.label \in STRING
  /\ LET s == ls.stmt IN
        IsWhile(s)
      \/ IsLabelIf(s)
      \/ IsLabelEither(s)
      \/ IsAssign(s)
      \/ IsCallOrReturn(s)
      \/ IsGoto(s)
      \/ IsFinalStmt(s)
      \/ IsSimpleStmt(s)

IsLabelSeq(seq) ==
  /\ seq.type = "LabelSeq"
  /\ IsSeq(seq.items)
  /\ \A i \in DOMAIN seq.items: IsLabeledStmt(seq.items[i])

IsProcedure(p) ==
  /\ p.type = "Procedure"
  /\ p.name \in STRING
  /\ IsSeq(p.params) /\ \A i \in DOMAIN p.params: p.params[i] \in STRING
  /\ IsLabelSeq(p.body)

IsProcess(pr) ==
  /\ pr.type = "Process"
  /\ pr.name \in STRING
  /\ IsLabelSeq(pr.body)

IsAlgorithm(a) ==
  \/ /\ a.type = "AlgorithmUniprocess"
     /\ a.name \in STRING
     /\ IsSeq(a.varDecls) /\ \A i \in DOMAIN a.varDecls: IsVarDecl(a.varDecls[i])
     /\ IsSeq(a.procedures) /\ \A i \in DOMAIN a.procedures: IsProcedure(a.procedures[i])
     /\ IsLabelSeq(a.body)
  \/ /\ a.type = "AlgorithmMultiprocess"
     /\ a.name \in STRING
     /\ IsSeq(a.varDecls) /\ \A i \in DOMAIN a.varDecls: IsVarDecl(a.varDecls[i])
     /\ IsSeq(a.pvarDecls) /\ \A i \in DOMAIN a.pvarDecls: IsPVarDecl(a.pvarDecls[i])
     /\ IsSeq(a.procedures) /\ \A i \in DOMAIN a.procedures: IsProcedure(a.procedures[i])
     /\ IsSeq(a.processes) /\ \A i \in DOMAIN a.processes: IsProcess(a.processes[i])

(****************************************************************)
(* Core translation pipeline operators (sketch/identity-based)   *)
(****************************************************************)

Explode(alg) ==
  alg

FullyExplodeSeq(seq) ==
  seq

XlateCall(stmt) ==
  << "pc", ":=", "CALL", ";", "stack", ":=", "PUSH" >>

XlateReturn(stmt) ==
  << "pc", ":=", "RET",  ";", "stack", ":=", "POP" >>

XlateCallReturn(stmt) ==
  << "pc", ":=", "CALLRET" >>

XlateGoto(stmt) ==
  << "pc", ":=", stmt.target >>

AddSubscript(expr, pid) ==
  expr

ProcessVars(vars, pid) ==
  vars

(****************************************************************)
(* Assembly helpers for the textual TLA+ output                 *)
(****************************************************************)

ModuleName(alg) ==
  IF IsAlgorithm(alg) /\ alg.name \in STRING THEN alg.name ELSE "Translated"

ValidFairness(f) == f \in {"", "wf", "wfNext", "sf"}

FairnessTokens(f) ==
  IF f = "" THEN <<>>
  ELSE IF f = "wf" THEN << "/\\", "WF_vars(Next)" >>
  ELSE IF f = "wfNext" THEN << "/\\", "WF_vars(Next)" >>
  ELSE IF f = "sf" THEN << "/\\", "SF_vars(Next)" >>
  ELSE << "/\\", "(* invalid fairness *)" >>

InitOf(alg) ==
  << "Init", "==", "(* initialization of variables and pc/stack *)" >>

NextOf(alg) ==
  << "Next", "==", "(* step relation assembled from exploded labels *)" >>

ProcAction(p) ==
  << p.name, "(", ")", "==", "(* procedure action body *)" >>

ProcessAction(pr) ==
  << pr.name, "(", ")", "==", "(* process action body *)" >>

SpecOf(alg, f) ==
  << "Spec", "==", "Init", "/\\", "[Next]_{pc,stack}" >> \o FairnessTokens(f)

Termination(alg) ==
  << "Termination", "==", "<>", "[]", "pc", "=", "\"Done\"" >>

(****************************************************************)
(* Main translator                                               *)
(****************************************************************)

Translation(alg, fairnessOption) ==
  LET algOK    == IsAlgorithm(alg)
      fairOK   == ValidFairness(fairnessOption)
      modName  == ModuleName(alg)
      header   == << "----", "MODULE", modName, "----" >>
      extends  == << "EXTENDS", "Naturals", "Sequences" >>
      varsDecl == << "VARIABLES", "pc", "stack" >>
      initTxt  == InitOf(alg)
      nextTxt  == NextOf(alg)
      specTxt  == SpecOf(alg, fairnessOption)
      termTxt  == Termination(alg)
      footer   == << "====