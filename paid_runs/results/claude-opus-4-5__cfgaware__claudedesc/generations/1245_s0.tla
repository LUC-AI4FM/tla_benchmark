---------------------------- MODULE XPlusCal ----------------------------
(***************************************************************************)
(* TLA+ specification of the translation from +CAL AST to TLA+             *)
(* Originally by Leslie Lamport, 2005                                       *)
(***************************************************************************)

EXTENDS Sequences, Integers, TLC, FiniteSets

CONSTANTS Object, Any

(***************************************************************************)
(* Basic type definitions                                                   *)
(***************************************************************************)

Lexeme == Seq(STRING)
TLAExpr == Seq(STRING)

(***************************************************************************)
(* Helper operators                                                         *)
(***************************************************************************)

SeqConcat(s) == 
    IF s = <<>> THEN <<>>
    ELSE LET RECURSIVE ConcatAll(_)
             ConcatAll(seq) == 
                 IF seq = <<>> THEN <<>>
                 ELSE Head(seq) \o ConcatAll(Tail(seq))
         IN ConcatAll(s)

Flatten(s) == SeqConcat(s)

StringToSeq(str) == <<str>>

Space == <<" ">>
Newline == <<"\n">>
Indent == <<"  ">>

(***************************************************************************)
(* AST Predicates - Mutually recursive predicates for AST validation       *)
(***************************************************************************)

RECURSIVE IsExpr(_)
IsExpr(e) == 
    \/ e = <<>>
    \/ (DOMAIN e \subseteq Nat /\ \A i \in DOMAIN e : e[i] \in STRING)

RECURSIVE IsVarDecl(_)
IsVarDecl(v) ==
    /\ v \in Object
    /\ "name" \in DOMAIN v
    /\ "init" \in DOMAIN v
    /\ v.name \in STRING
    /\ IsExpr(v.init)

RECURSIVE IsPVarDecl(_)
IsPVarDecl(v) ==
    /\ v \in Object
    /\ "name" \in DOMAIN v
    /\ "init" \in DOMAIN v
    /\ v.name \in STRING
    /\ IsExpr(v.init)

RECURSIVE IsAssign(_)
IsAssign(a) ==
    /\ a \in Object
    /\ "type" \in DOMAIN a
    /\ a.type = "assignment"
    /\ "lhs" \in DOMAIN a
    /\ "rhs" \in DOMAIN a
    /\ IsExpr(a.lhs)
    /\ IsExpr(a.rhs)

RECURSIVE IsGoto(_)
IsGoto(g) ==
    /\ g \in Object
    /\ "type" \in DOMAIN g
    /\ g.type = "goto"
    /\ "label" \in DOMAIN g
    /\ g.label \in STRING

RECURSIVE IsCallOrReturn(_)
IsCallOrReturn(c) ==
    /\ c \in Object
    /\ "type" \in DOMAIN c
    /\ c.type \in {"call", "return", "callReturn"}

RECURSIVE IsSimpleStmt(_)
IsSimpleStmt(s) ==
    \/ IsAssign(s)
    \/ IsGoto(s)
    \/ IsCallOrReturn(s)
    \/ (s \in Object /\ "type" \in DOMAIN s /\ s.type = "skip")
    \/ (s \in Object /\ "type" \in DOMAIN s /\ s.type = "print")
    \/ (s \in Object /\ "type" \in DOMAIN s /\ s.type = "assert")

RECURSIVE IsFinalStmt(_)
IsFinalStmt(f) ==
    \/ IsSimpleStmt(f)
    \/ (f \in Object /\ "type" \in DOMAIN f /\ f.type = "if")
    \/ (f \in Object /\ "type" \in DOMAIN f /\ f.type = "either")
    \/ (f \in Object /\ "type" \in DOMAIN f /\ f.type = "with")

RECURSIVE IsLabelSeq(_)
IsLabelSeq(ls) ==
    /\ DOMAIN ls \subseteq Nat
    /\ \A i \in DOMAIN ls : IsLabeledStmt(ls[i])

RECURSIVE IsLabelIf(_)
IsLabelIf(li) ==
    /\ li \in Object
    /\ "type" \in DOMAIN li
    /\ li.type = "labelIf"
    /\ "test" \in DOMAIN li
    /\ "then" \in DOMAIN li
    /\ "else" \in DOMAIN li

RECURSIVE IsLabelEither(_)
IsLabelEither(le) ==
    /\ le \in Object
    /\ "type" \in DOMAIN le
    /\ le.type = "labelEither"
    /\ "clauses" \in DOMAIN le

RECURSIVE IsWhile(_)
IsWhile(w) ==
    /\ w \in Object
    /\ "type" \in DOMAIN w
    /\ w.type = "while"
    /\ "test" \in DOMAIN w
    /\ "body" \in DOMAIN w

RECURSIVE IsLabeledStmt(_)
IsLabeledStmt(ls) ==
    /\ ls \in Object
    /\ "label" \in DOMAIN ls
    /\ ls.label \in STRING
    /\ "stmts" \in DOMAIN ls

RECURSIVE IsProcedure(_)
IsProcedure(p) ==
    /\ p \in Object
    /\ "type" \in DOMAIN p
    /\ p.type = "procedure"
    /\ "name" \in DOMAIN p
    /\ "params" \in DOMAIN p
    /\ "vars" \in DOMAIN p
    /\ "body" \in DOMAIN p

RECURSIVE IsProcess(_)
IsProcess(p) ==
    /\ p \in Object
    /\ "type" \in DOMAIN p
    /\ p.type = "process"
    /\ "name" \in DOMAIN p
    /\ "id" \in DOMAIN p
    /\ "vars" \in DOMAIN p
    /\ "body" \in DOMAIN p

IsUniprocessAlgorithm(alg) ==
    /\ alg \in Object
    /\ "type" \in DOMAIN alg
    /\ alg.type = "uniprocess"
    /\ "name" \in DOMAIN alg
    /\ "vars" \in DOMAIN alg
    /\ "body" \in DOMAIN alg

IsMultiprocessAlgorithm(alg) ==
    /\ alg \in Object
    /\ "type" \in DOMAIN alg
    /\ alg.type = "multiprocess"
    /\ "name" \in DOMAIN alg
    /\ "vars" \in DOMAIN alg
    /\ "procs" \in DOMAIN alg

IsAlgorithm(alg) ==
    \/ IsUniprocessAlgorithm(alg)
    \/ IsMultiprocessAlgorithm(alg)

(***************************************************************************)
(* Translation Helper Functions                                             *)
(***************************************************************************)

AddSubscript(expr, subscript) ==
    IF subscript = <<>> THEN expr
    ELSE expr \o <<"[">> \o subscript \o <<"]">>

ProcessVars(proc) ==
    IF "vars" \in DOMAIN proc THEN proc.vars ELSE <<>>

RECURSIVE ExplodeStmt(_)
ExplodeStmt(stmt) ==
    IF stmt \in Object /\ "type" \in DOMAIN stmt
    THEN CASE stmt.type = "while" -> 
              [label |-> "whileLabel", stmts |-> <<stmt>>]
         [] stmt.type = "labelIf" ->
              [label |-> "ifLabel", stmts |-> <<stmt>>]
         [] stmt.type = "labelEither" ->
              [label |-> "eitherLabel", stmts |-> <<stmt>>]
         [] OTHER -> [label |-> "simpleLabel", stmts |-> <<stmt>>]
    ELSE [label |-> "unknown", stmts |-> <<stmt>>]

RECURSIVE Explode(_)
Explode(stmts) ==
    IF stmts = <<>> THEN <<>>
    ELSE <<ExplodeStmt(Head(stmts))>> \o Explode(Tail(stmts))

RECURSIVE FullyExplodeSeq(_)
FullyExplodeSeq(labeledStmts) ==
    IF labeledStmts = <<>> THEN <<>>
    ELSE Explode(Head(labeledStmts).stmts) \o FullyExplodeSeq(Tail(labeledStmts))

XlateGoto(label) ==
    <<"pc">> \o <<"'">> \o <<"=">> \o <<"\"">> \o <<label>> \o <<"\"">>

XlateCall(procName, args) ==
    <<"stack">> \o <<"'">> \o <<"=">> \o <<"<<">> \o 
    <<"[procedure |->">> \o <<"\"">> \o <<procName>> \o <<"\"">> \o <<"]">> \o
    <<">>">> \o <<"\\o">> \o <<"stack">>

XlateReturn ==
    <<"pc">> \o <<"'">> \o <<"=">> \o <<"Head(stack).pc">> \o <<"/\\">> \o
    <<"stack">> \o <<"'">> \o <<"=">> \o <<"Tail(stack)">>

XlateCallReturn(procName, args) ==
    XlateCall(procName, args) \o <<"/\\">> \o XlateReturn

(***************************************************************************)
(* TLA+ Code Generation                                                     *)
(***************************************************************************)

GenVarDecls(vars) ==
    IF vars = <<>> THEN <<>>
    ELSE LET RECURSIVE GenVars(_)
             GenVars(vs) ==
                 IF vs = <<>> THEN <<>>
                 ELSE <<Head(vs).name>> \o 
                      (IF Tail(vs) # <<>> THEN <<",">> ELSE <<>>) \o
                      GenVars(Tail(vs))
         IN <<"VARIABLES">> \o Space \o GenVars(vars) \o Newline

GenVarInits(vars) ==
    IF vars = <<>> THEN <<"TRUE">>
    ELSE LET RECURSIVE GenInits(_)
             GenInits(vs) ==
                 IF vs = <<>> THEN <<>>
                 ELSE <<Head(vs).name>> \o <<"=">> \o Head(vs).init \o
                      (IF Tail(vs) # <<>> THEN <<"/\\">> ELSE <<>>) \o
                      GenInits(Tail(vs))
         IN GenInits(vars)

GenInit(alg) ==
    <<"Init">> \o <<"==">> \o Newline \o
    Indent \o <<"/\\">> \o Space \o <<"pc">> \o <<"=">> \o <<"\"start\"">> \o Newline \o
    Indent \o <<"/\\">> \o Space \o GenVarInits(alg.vars)

GenNext(alg) ==
    <<"Next">> \o <<"==">> \o Newline \o
    Indent \o <<"\\/">> \o Space \o <<"ActionStep">> \o Newline \o
    Indent \o <<"\\/">> \o Space \o <<"Terminating">>

GenSpec(fairnessOption) ==
    LET baseSpc == <<"Spec">> \o <<"==">> \o Space \o <<"Init">> \o <<"/\\">> \o <<"[][Next]_vars">>
        fairness == CASE fairnessOption = "" -> <<>>
                    [] fairnessOption = "wf" -> <<"/\\">> \o <<"WF_vars(Next)">>
                    [] fairnessOption = "wfNext" -> <<"/\\">> \o <<"WF_vars(Next)">>
                    [] fairnessOption = "sf" -> <<"/\\">> \o <<"SF_vars(Next)">>
                    [] OTHER -> <<>>
    IN baseSpc \o fairness

GenTermination ==
    <<"Termination">> \o <<"==">> \o Space \o <<"<>[](pc = \"Done\")">>

(***************************************************************************)
(* Main Translation Operator                                                *)
(***************************************************************************)

Translation(alg, fairnessOption) ==
    IF ~IsAlgorithm(alg) THEN <<"ERROR: Invalid algorithm AST">>
    ELSE LET header == <<"----">> \o <<"MODULE">> \o Space \o <<alg.name>> \o Space \o <<"----">> \o Newline
             extends == <<"EXTENDS">> \o Space \o <<"Naturals, Sequences">> \o Newline \o Newline
             varDecls == GenVarDecls(alg.vars) \o 
                        <<"VARIABLES">> \o Space \o <<"pc">> \o Newline \o Newline
             initDef == GenInit(alg) \o Newline \o Newline
             nextDef == GenNext(alg) \o Newline \o Newline
             specDef == GenSpec(fairnessOption) \o Newline \o Newline
             termDef == GenTermination \o Newline
             footer == <<"====