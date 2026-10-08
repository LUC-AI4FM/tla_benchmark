---------------------------- MODULE OldPlusCal ----------------------------

EXTENDS Integers, Sequences, TLC

CONSTANTS ast, fairness, Object, Any

-----------------------------------------------------------------------------

(* Helper operators *)

Len2(s) == Len(s)

Append2(s, e) == Append(s, e)

Concat(s1, s2) == s1 \o s2

FlattenSeq(seqs) == 
    IF seqs = <<>> THEN <<>>
    ELSE LET RECURSIVE Flat(_)
             Flat(ss) == IF ss = <<>> THEN <<>>
                         ELSE Head(ss) \o Flat(Tail(ss))
         IN Flat(seqs)

-----------------------------------------------------------------------------

(* TLA+ expressions are sequences of string lexemes *)

IsSeqOfStrings(e) == 
    /\ e \in Seq(STRING)

IsTLAExpr(e) == IsSeqOfStrings(e)

-----------------------------------------------------------------------------

(* Variable declaration predicates *)

IsVarDecl(v) ==
    /\ v \in Object
    /\ "name" \in DOMAIN v
    /\ "initial" \in DOMAIN v
    /\ v.name \in STRING
    /\ IsTLAExpr(v.initial)

IsVarDeclSeq(vs) ==
    /\ vs \in Seq(Object)
    /\ \A i \in 1..Len(vs) : IsVarDecl(vs[i])

-----------------------------------------------------------------------------

(* Simple statement predicates *)

IsAssignment(stmt) ==
    /\ stmt \in Object
    /\ "type" \in DOMAIN stmt
    /\ stmt.type = "assignment"
    /\ "lhs" \in DOMAIN stmt
    /\ "rhs" \in DOMAIN stmt

IsIf(stmt) ==
    /\ stmt \in Object
    /\ "type" \in DOMAIN stmt
    /\ stmt.type = "if"

IsEither(stmt) ==
    /\ stmt \in Object
    /\ "type" \in DOMAIN stmt
    /\ stmt.type = "either"

IsWith(stmt) ==
    /\ stmt \in Object
    /\ "type" \in DOMAIN stmt
    /\ stmt.type = "with"

IsWhen(stmt) ==
    /\ stmt \in Object
    /\ "type" \in DOMAIN stmt
    /\ stmt.type = "when"

IsPrint(stmt) ==
    /\ stmt \in Object
    /\ "type" \in DOMAIN stmt
    /\ stmt.type = "print"

IsAssert(stmt) ==
    /\ stmt \in Object
    /\ "type" \in DOMAIN stmt
    /\ stmt.type = "assert"

IsSkip(stmt) ==
    /\ stmt \in Object
    /\ "type" \in DOMAIN stmt
    /\ stmt.type = "skip"

IsCall(stmt) ==
    /\ stmt \in Object
    /\ "type" \in DOMAIN stmt
    /\ stmt.type = "call"

IsReturn(stmt) ==
    /\ stmt \in Object
    /\ "type" \in DOMAIN stmt
    /\ stmt.type = "return"

IsCallReturn(stmt) ==
    /\ stmt \in Object
    /\ "type" \in DOMAIN stmt
    /\ stmt.type = "callReturn"

IsGoto(stmt) ==
    /\ stmt \in Object
    /\ "type" \in DOMAIN stmt
    /\ stmt.type = "goto"

IsSimpleStmt(stmt) ==
    \/ IsAssignment(stmt)
    \/ IsIf(stmt)
    \/ IsEither(stmt)
    \/ IsWith(stmt)
    \/ IsWhen(stmt)
    \/ IsPrint(stmt)
    \/ IsAssert(stmt)
    \/ IsSkip(stmt)
    \/ IsCall(stmt)
    \/ IsReturn(stmt)
    \/ IsCallReturn(stmt)
    \/ IsGoto(stmt)

-----------------------------------------------------------------------------

(* While loop predicate *)

IsWhile(stmt) ==
    /\ stmt \in Object
    /\ "type" \in DOMAIN stmt
    /\ stmt.type = "while"
    /\ "condition" \in DOMAIN stmt
    /\ "body" \in DOMAIN stmt

-----------------------------------------------------------------------------

(* Labeled statement predicate *)

IsLabeledStmt(ls) ==
    /\ ls \in Object
    /\ "label" \in DOMAIN ls
    /\ "stmts" \in DOMAIN ls
    /\ ls.label \in STRING

IsLabeledStmtSeq(lss) ==
    /\ lss \in Seq(Object)
    /\ \A i \in 1..Len(lss) : IsLabeledStmt(lss[i])

-----------------------------------------------------------------------------

(* Procedure predicate *)

IsProcedure(proc) ==
    /\ proc \in Object
    /\ "type" \in DOMAIN proc
    /\ proc.type = "procedure"
    /\ "name" \in DOMAIN proc
    /\ "params" \in DOMAIN proc
    /\ "vars" \in DOMAIN proc
    /\ "body" \in DOMAIN proc

IsProcedureSeq(procs) ==
    /\ procs \in Seq(Object)
    /\ \A i \in 1..Len(procs) : IsProcedure(procs[i])

-----------------------------------------------------------------------------

(* Process predicate *)

IsProcess(p) ==
    /\ p \in Object
    /\ "type" \in DOMAIN p
    /\ p.type = "process"
    /\ "name" \in DOMAIN p
    /\ "id" \in DOMAIN p
    /\ "vars" \in DOMAIN p
    /\ "body" \in DOMAIN p

IsProcessSeq(ps) ==
    /\ ps \in Seq(Object)
    /\ \A i \in 1..Len(ps) : IsProcess(ps[i])

-----------------------------------------------------------------------------

(* Algorithm predicates *)

IsUniprocessAlgorithm(alg) ==
    /\ alg \in Object
    /\ "type" \in DOMAIN alg
    /\ alg.type = "uniprocess"
    /\ "name" \in DOMAIN alg
    /\ "vars" \in DOMAIN alg
    /\ "procedures" \in DOMAIN alg
    /\ "body" \in DOMAIN alg

IsMultiprocessAlgorithm(alg) ==
    /\ alg \in Object
    /\ "type" \in DOMAIN alg
    /\ alg.type = "multiprocess"
    /\ "name" \in DOMAIN alg
    /\ "vars" \in DOMAIN alg
    /\ "procedures" \in DOMAIN alg
    /\ "processes" \in DOMAIN alg

IsAlgorithm(alg) ==
    \/ IsUniprocessAlgorithm(alg)
    \/ IsMultiprocessAlgorithm(alg)

-----------------------------------------------------------------------------

(* Fairness option validation *)

IsValidFairnessOption(opt) ==
    opt \in {"", "wf", "wfNext", "sf"}

-----------------------------------------------------------------------------

(* Explode operators - transform labeled statements into atomic actions *)

RECURSIVE ExplodeStmt(_, _)
ExplodeStmt(stmt, ctx) ==
    IF IsSimpleStmt(stmt) THEN <<stmt>>
    ELSE IF IsWhile(stmt) THEN <<stmt>>
    ELSE <<stmt>>

RECURSIVE ExplodeSeq(_)
ExplodeSeq(stmts) ==
    IF stmts = <<>> THEN <<>>
    ELSE ExplodeStmt(Head(stmts), {}) \o ExplodeSeq(Tail(stmts))

Explode(labeledStmt) ==
    [label |-> labeledStmt.label,
     stmts |-> ExplodeSeq(labeledStmt.stmts)]

RECURSIVE FullyExplodeSeq(_)
FullyExplodeSeq(labeledStmts) ==
    IF labeledStmts = <<>> THEN <<>>
    ELSE <<Explode(Head(labeledStmts))>> \o FullyExplodeSeq(Tail(labeledStmts))

-----------------------------------------------------------------------------

(* Translation helpers *)

TranslateVarDecl(v) ==
    <<v.name, " = ">> \o v.initial

TranslateVarDecls(vars) ==
    IF vars = <<>> THEN <<>>
    ELSE LET RECURSIVE Trans(_)
             Trans(vs) == IF vs = <<>> THEN <<>>
                          ELSE TranslateVarDecl(Head(vs)) \o 
                               (IF Tail(vs) = <<>> THEN <<>> ELSE <<" /\\ ">>) \o
                               Trans(Tail(vs))
         IN Trans(vars)

TranslateInit(alg) ==
    <<"Init == ">> \o TranslateVarDecls(alg.vars)

TranslateNext(alg) ==
    <<"Next == ", "TRUE">>

TranslateProcSet(alg) ==
    IF IsMultiprocessAlgorithm(alg) 
    THEN <<"ProcSet == ", "UNION {}">>
    ELSE <<>>

TranslateVars(alg) ==
    <<"vars == << ">> \o 
    (IF alg.vars = <<>> THEN <<>> ELSE <<Head(alg.vars).name>>) \o
    <<" >>">>

TranslateSpec(alg, fairOpt) ==
    LET base == <<"Spec == ", "Init /\\ [][Next]_vars">>
    IN IF fairOpt = "" THEN base
       ELSE IF fairOpt = "wf" THEN base \o <<" /\\ WF_vars(Next)">>
       ELSE IF fairOpt = "wfNext" THEN base \o <<" /\\ WF_vars(Next)">>
       ELSE IF fairOpt = "sf" THEN base \o <<" /\\ SF_vars(Next)">>
       ELSE base

TranslateTermination(alg) ==
    <<"Termination == ", "<>[]( \\A self \\in ProcSet : pc[self] = \"Done\" )">>

TranslateProcedures(procs) ==
    IF procs = <<>> THEN <<>>
    ELSE <<"(* Procedures *)">>

TranslateProcesses(procs) ==
    IF procs = <<>> THEN <<>>
    ELSE <<"(* Processes *)">>

-----------------------------------------------------------------------------

(* Main Translation operator *)

Translation(alg, fairnessOption) ==
    LET header == <<"(* BEGIN TRANSLATION *)">>
        initDef == TranslateInit(alg)
        nextDef == TranslateNext(alg)
        procSetDef == TranslateProcSet(alg)
        varsDef == TranslateVars(alg)
        specDef == TranslateSpec(alg, fairnessOption)
        termDef == TranslateTermination(alg)
        footer == <<"(* END TRANSLATION *)">>
        procDefs == IF "procedures" \in DOMAIN alg 
                    THEN TranslateProcedures(alg.procedures)
                    ELSE <<>>
        processDefs == IF IsMultiprocessAlgorithm(alg)
                       THEN TranslateProcesses(alg.processes)
                       ELSE <<>>
    IN header \o varsDef \o procDefs \o processDefs \o 
       initDef \o nextDef \o procSetDef \o specDef \o termDef \o footer

-----------------------------------------------------------------------------

(* Well-formedness check *)

IsWellFormedAlgorithm(alg) ==
    /\ IsAlgorithm(alg)
    /\ "vars" \in DOMAIN alg
    /\ IsVarDeclSeq(alg.vars)
    /\ "procedures" \in DOMAIN alg
    /\ IsProcedureSeq(alg.procedures)
    /\ IF IsMultiprocessAlgorithm(alg)
       THEN /\ "processes" \in DOMAIN alg
            /\ IsProcessSeq(alg.processes)
       ELSE /\ "body" \in DOMAIN alg
            /\ IsLabeledStmtSeq(alg.body)

-----------------------------------------------------------------------------

(* ASSUME statement for TLC execution *)

ASSUME 
    /\ IsValidFairnessOption(fairness)
    /\ PrintT(Translation(ast, fairness))

=============================================================================