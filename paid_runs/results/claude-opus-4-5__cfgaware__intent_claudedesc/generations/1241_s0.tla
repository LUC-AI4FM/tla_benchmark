---------------------------- MODULE PlusCalTranslation ----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets

CONSTANTS Object, Any

(* Abstract Syntax Tree Node Types *)
VarDecl == [name: Any, init: Any]
PVarDecl == [name: Any, init: Any, isRef: Any]

(* Expression types - simplified representation *)
Expr == Any
Label == Any
Name == Any

(* Statement types *)
AssignPair == [lhs: Any, rhs: Any]
Assignment == [type: {"assignment"}, pairs: Any]
IfStmt == [type: {"if"}, cond: Any, thenPart: Any, elsePart: Any]
EitherStmt == [type: {"either"}, branches: Any]
WithStmt == [type: {"with"}, var: Any, inSet: Any, body: Any]
WhileStmt == [type: {"while"}, cond: Any, body: Any]
CallStmt == [type: {"call"}, proc: Any, args: Any]
ReturnStmt == [type: {"return"}]
CallReturnStmt == [type: {"callReturn"}, proc: Any, args: Any]
GotoStmt == [type: {"goto"}, label: Any]
PrintStmt == [type: {"print"}, expr: Any]
AssertStmt == [type: {"assert"}, expr: Any]
SkipStmt == [type: {"skip"}]
WhenStmt == [type: {"when"}, cond: Any]
AwaitStmt == [type: {"await"}, cond: Any]

Statement == Assignment \cup IfStmt \cup EitherStmt \cup WithStmt \cup 
             WhileStmt \cup CallStmt \cup ReturnStmt \cup CallReturnStmt \cup
             GotoStmt \cup PrintStmt \cup AssertStmt \cup SkipStmt \cup 
             WhenStmt \cup AwaitStmt

LabeledStmts == [label: Any, stmts: Any]
LabeledStmtSeq == Seq(LabeledStmts)

ProcedureDef == [type: {"procedure"}, name: Any, params: Any, pvars: Any, body: Any]
ProcessDef == [type: {"process"}, name: Any, id: Any, vars: Any, body: Any, fairness: Any]

UniprocessAlg == [type: {"uniprocess"}, name: Any, vars: Any, procs: Any, body: Any]
MultiprocessAlg == [type: {"multiprocess"}, name: Any, vars: Any, procs: Any, processes: Any]

Algorithm == UniprocessAlg \cup MultiprocessAlg

(* Fairness options *)
NoFairness == "none"
WeakFairnessAll == "wfAll"
WeakFairnessNext == "wfNext"
StrongFairnessAll == "sfAll"

FairnessOption == {NoFairness, WeakFairnessAll, WeakFairnessNext, StrongFairnessAll}

(* Helper operators for sequence manipulation *)
Concat(s1, s2) == s1 \o s2
Flatten(seqOfSeq) == 
    IF seqOfSeq = <<>> THEN <<>>
    ELSE Head(seqOfSeq) \o Flatten(Tail(seqOfSeq))

(* String/Lexeme helpers *)
Str(s) == s
Newline == "\n"
Space == " "
Indent(n) == IF n <= 0 THEN "" ELSE " " \o Indent(n-1)

(* Replace placeholder names with actual names *)
ReplacePlaceholders(lexeme) ==
    CASE lexeme = "@pc@" -> "pc"
      [] lexeme = "@stack@" -> "stack"
      [] OTHER -> lexeme

ReplacePlaceholdersInSeq(lexemes) ==
    [i \in DOMAIN lexemes |-> ReplacePlaceholders(lexemes[i])]

(* Extract all labels from a labeled statement sequence *)
RECURSIVE ExtractLabels(_)
ExtractLabels(body) ==
    IF body = <<>> THEN {}
    ELSE {Head(body).label} \cup ExtractLabels(Tail(body))

(* Extract all labels from procedures *)
RECURSIVE ExtractProcLabels(_)
ExtractProcLabels(procs) ==
    IF procs = <<>> THEN {}
    ELSE ExtractLabels(Head(procs).body) \cup ExtractProcLabels(Tail(procs))

(* Extract all labels from processes *)
RECURSIVE ExtractProcessLabels(_)
ExtractProcessLabels(processes) ==
    IF processes = <<>> THEN {}
    ELSE ExtractLabels(Head(processes).body) \cup ExtractProcessLabels(Tail(processes))

(* Get all labels in an algorithm *)
AllLabels(alg) ==
    IF alg.type = "uniprocess" THEN
        ExtractLabels(alg.body) \cup ExtractProcLabels(alg.procs) \cup {"Done"}
    ELSE
        ExtractProcessLabels(alg.processes) \cup ExtractProcLabels(alg.procs) \cup {"Done"}

(* Get all variable names *)
RECURSIVE ExtractVarNames(_)
ExtractVarNames(vars) ==
    IF vars = <<>> THEN {}
    ELSE {Head(vars).name} \cup ExtractVarNames(Tail(vars))

(* Get process names *)
RECURSIVE ExtractProcessNames(_)
ExtractProcessNames(processes) ==
    IF processes = <<>> THEN {}
    ELSE {Head(processes).name} \cup ExtractProcessNames(Tail(processes))

(* Get procedure names *)
RECURSIVE ExtractProcNames(_)
ExtractProcNames(procs) ==
    IF procs = <<>> THEN {}
    ELSE {Head(procs).name} \cup ExtractProcNames(Tail(procs))

(* Check if algorithm is multiprocess *)
IsMultiprocess(alg) == alg.type = "multiprocess"

(* Translate expression to lexemes *)
RECURSIVE TranslateExpr(_)
TranslateExpr(expr) ==
    IF expr = <<>> THEN <<>>
    ELSE <<ToString(expr)>>

(* Translate variable with optional self subscript *)
TranslateVar(varName, isMulti) ==
    IF isMulti THEN <<varName, "[", "self", "]">>
    ELSE <<varName>>

(* Translate assignment pair *)
TranslateAssignPair(pair, isMulti) ==
    LET lhs == TranslateVar(pair.lhs, isMulti)
        rhs == TranslateExpr(pair.rhs)
    IN lhs \o <<"'">> \o <<"=">> \o rhs

(* Translate multiple assignment pairs *)
RECURSIVE TranslateAssignPairs(_, _)
TranslateAssignPairs(pairs, isMulti) ==
    IF pairs = <<>> THEN <<>>
    ELSE IF Len(pairs) = 1 THEN TranslateAssignPair(Head(pairs), isMulti)
    ELSE TranslateAssignPair(Head(pairs), isMulti) \o <<"/\\">> \o 
         TranslateAssignPairs(Tail(pairs), isMulti)

(* Generate pc assignment *)
PCAssign(nextLabel, isMulti) ==
    IF isMulti THEN <<"pc", "'", "[", "self", "]", "=", "\"", nextLabel, "\"">>
    ELSE <<"pc", "'", "=", "\"", nextLabel, "\"">>

(* Generate stack push for procedure call *)
StackPush(returnLabel, procName, args, isMulti) ==
    LET stackVar == IF isMulti THEN <<"stack", "[", "self", "]">> ELSE <<"stack">>
        newEntry == <<"[", "procedure", "|->", "\"", procName, "\"", ",">>
        returnPart == <<"pc", "|->", "\"", returnLabel, "\"">>
    IN <<"stack", "'", "=">> \o 
       IF isMulti THEN <<"[", "stack", "EXCEPT", "!", "[", "self", "]", "=">>
       ELSE <<"">> \o
       <<"<<", "[", "procedure", "|->", "\"", procName, "\"", ",", 
         "pc", "|->", "\"", returnLabel, "\"", "]", ">>">> \o
       <<"\\o">> \o stackVar \o
       IF isMulti THEN <<"]">> ELSE <<>>

(* Generate stack pop for return *)
StackPop(isMulti) ==
    LET stackVar == IF isMulti THEN <<"stack", "[", "self", "]">> ELSE <<"stack">>
    IN <<"stack", "'", "=">> \o
       IF isMulti THEN <<"[", "stack", "EXCEPT", "!", "[", "self", "]", "=", 
                        "Tail", "(", "@", ")", "]">>
       ELSE <<"Tail", "(", "stack", ")">>

(* Get next label or Done *)
NextLabel(body, idx) ==
    IF idx >= Len(body) THEN "Done"
    ELSE body[idx + 1].label

(* Translate a single statement *)
RECURSIVE TranslateStmt(_, _, _, _)
TranslateStmt(stmt, nextLabel, isMulti, procName) ==
    CASE stmt.type = "assignment" ->
        TranslateAssignPairs(stmt.pairs, isMulti) \o <<"/\\">> \o PCAssign(nextLabel, isMulti)
    
    [] stmt.type = "if" ->
        <<"IF">> \o TranslateExpr(stmt.cond) \o <<Newline>> \o
        <<"THEN">> \o TranslateStmt(stmt.thenPart, nextLabel, isMulti, procName) \o
        <<"ELSE">> \o TranslateStmt(stmt.elsePart, nextLabel, isMulti, procName)
    
    [] stmt.type = "either" ->
        <<"\\/">> \o TranslateStmt(Head(stmt.branches), nextLabel, isMulti, procName)
    
    [] stmt.type = "with" ->
        <<"\\E", stmt.var, "\\in">> \o TranslateExpr(stmt.inSet) \o <<":">> \o
        TranslateStmt(stmt.body, nextLabel, isMulti, procName)
    
    [] stmt.type = "while" ->
        <<"IF">> \o TranslateExpr(stmt.cond) \o
        <<"THEN">> \o TranslateStmt(stmt.body, nextLabel, isMulti, procName) \o
        <<"ELSE">> \o PCAssign(nextLabel, isMulti)
    
    [] stmt.type = "call" ->
        StackPush(nextLabel, stmt.proc, stmt.args, isMulti) \o <<"/\\">> \o
        PCAssign(stmt.proc, isMulti)
    
    [] stmt.type = "return" ->
        StackPop(isMulti) \o <<"/\\">> \o
        IF isMulti THEN <<"pc", "'", "[", "self", "]", "=", "Head", "(", "stack", "[", "self", "]", ")", ".", "pc">>
        ELSE <<"pc", "'", "=", "Head", "(", "stack", ")", ".", "pc">>
    
    [] stmt.type = "callReturn" ->
        StackPush(nextLabel, stmt.proc, stmt.args, isMulti) \o <<"/\\">> \o
        PCAssign(stmt.proc, isMulti)
    
    [] stmt.type = "goto" ->
        PCAssign(stmt.label, isMulti)
    
    [] stmt.type = "print" ->
        <<"PrintT", "(">> \o TranslateExpr(stmt.expr) \o <<")", "/\\">> \o PCAssign(nextLabel, isMulti)
    
    [] stmt.type = "assert" ->
        <<"Assert", "(">> \o TranslateExpr(stmt.expr) \o <<",", "\"Assertion Failed\"", ")", "/\\">> \o 
        PCAssign(nextLabel, isMulti)
    
    [] stmt.type = "skip" ->
        PCAssign(nextLabel, isMulti)
    
    [] stmt.type = "when" ->
        TranslateExpr(stmt.cond) \o <<"/\\">> \o PCAssign(nextLabel, isMulti)
    
    [] stmt.type = "await" ->
        TranslateExpr(stmt.cond) \o <<"/\\">> \o PCAssign(nextLabel, isMulti)
    
    [] OTHER -> <<"TRUE", "/\\">> \o PCAssign(nextLabel, isMulti)

(* Translate statements in a labeled block *)
RECURSIVE TranslateStmts(_, _, _, _)
TranslateStmts(stmts, nextLabel, isMulti, procName) ==
    IF stmts = <<>> THEN PCAssign(nextLabel, isMulti)
    ELSE IF Len(stmts) = 1 THEN TranslateStmt(Head(stmts), nextLabel, isMulti, procName)
    ELSE TranslateStmt(Head(stmts), nextLabel, isMulti, procName) \o <<"/\\">> \o
         TranslateStmts(Tail(stmts), nextLabel, isMulti, procName)

(* Translate a labeled statement block to an action *)
TranslateLabeledStmt(ls, nextLabel, isMulti, procName) ==
    LET actionName == ls.label
        pcGuard == IF isMulti 
                   THEN <<"pc", "[", "self", "]", "=", "\"", ls.label, "\"">>
                   ELSE <<"pc", "=", "\"", ls.label, "\"">>
        body == TranslateStmts(ls.stmts, nextLabel, isMulti, procName)
    IN <<actionName, "(", IF isMulti THEN "self" ELSE "", ")", "==", Newline>> \o
       pcGuard \o <<"/\\", Newline>> \o body \o <<Newline, Newline>>

(* Translate all labeled statements in a body *)
RECURSIVE TranslateLabeledStmts(_, _, _, _)
TranslateLabeledStmts(body, idx, isMulti, procName) ==
    IF idx > Len(body) THEN <<>>
    ELSE LET nextLabel == IF idx >= Len(body) THEN "Done" ELSE body[idx + 1].label
         IN TranslateLabeledStmt(body[idx], nextLabel, isMulti, procName) \o
            TranslateLabeledStmts(body, idx + 1, isMulti, procName)

(* Translate procedure definition *)
TranslateProcedure(proc, isMulti) ==
    <<"(* Procedure", proc.name, "*)", Newline>> \o
    TranslateLabeledStmts(proc.body, 1, isMulti, proc.name)

(* Translate all procedures *)
RECURSIVE TranslateProcedures(_, _)
TranslateProcedures(procs, isMulti) ==
    IF procs = <<>> THEN <<>>
    ELSE TranslateProcedure(Head(procs), isMulti) \o TranslateProcedures(Tail(procs), isMulti)

(* Translate process definition *)
TranslateProcess(proc) ==
    <<"(* Process", proc.name, "*)", Newline>> \o
    TranslateLabeledStmts(proc.body, 1, TRUE, proc.name)

(* Translate all processes *)
RECURSIVE TranslateProcesses(_)
TranslateProcesses(processes) ==
    IF processes = <<>> THEN <<>>
    ELSE TranslateProcess(Head(processes)) \o TranslateProcesses(Tail(processes))

(* Generate variable initialization *)
RECURSIVE TranslateVarInits(_)
TranslateVarInits(vars) ==
    IF vars = <<>> THEN <<>>
    ELSE IF Len(vars) = 1 THEN 
        <<Head(vars).name, "=">> \o TranslateExpr(Head(vars).init)
    ELSE <<Head(vars).name, "=">> \o TranslateExpr(Head(vars).init) \o <<"/\\", Newline>> \o
         TranslateVarInits(Tail(vars))

(* Generate ProcSet for multiprocess *)
RECURSIVE TranslateProcSet(_)
TranslateProcSet(processes) ==
    IF processes = <<>> THEN <<"{}">>
    ELSE IF Len(processes) = 1 THEN TranslateExpr(Head(processes).id)
    ELSE TranslateExpr(Head(processes).id) \o <<"\\cup">> \o TranslateProcSet(Tail(processes))

(* Generate Init definition *)
TranslateInit(alg) ==
    LET isMulti == IsMultiprocess(alg)
        globalVars == TranslateVarInits(alg.vars)
        pcInit == IF isMulti 
                  THEN <<"pc", "=", "[", "self", "\\in", "ProcSet", "|->", "CASE">> \o
                       <<"TRUE", "->", "\"Done\"", "]">>
                  ELSE <<"pc", "=", "\"">> \o 
                       (IF alg.body = <<>> THEN <<"Done">> ELSE <<Head(alg.body).label>>) \o
                       <<"\"">>
        stackInit == IF alg.procs = <<>> THEN <<>>
                     ELSE IF isMulti 
                          THEN <<"stack", "=", "[", "self", "\\in", "ProcSet", "|->", "<<>>", "]">>
                          ELSE <<"stack", "=", "<<>>">>
    IN <<"Init", "==", Newline>> \o
       globalVars \o (IF globalVars = <<>> THEN <<>> ELSE <<"/\\", Newline>>) \o
       pcInit \o 
       (IF stackInit = <<>> THEN <<>> ELSE <<"/\\", Newline>> \o stackInit) \o
       <<Newline, Newline>>

(* Generate action disjunction for Next *)
RECURSIVE GenerateActionDisj(_, _, _)
GenerateActionDisj(labels, isMulti, procName) ==
    IF labels = {} THEN <<"FALSE">>
    ELSE LET label == CHOOSE l \in labels : TRUE
             rest == labels \ {label}
             action == IF isMulti 
                       THEN <<label, "(", "self", ")">>
                       ELSE <<label>>
         IN action \o (IF rest = {} THEN <<>> ELSE <<"\\/">> \o GenerateActionDisj(rest, isMulti, procName))

(* Generate Next definition *)
TranslateNext(alg) ==
    LET isMulti == IsMultiprocess(alg)
        labels == AllLabels(alg) \ {"Done"}
    IN <<"Next", "==", Newline>> \o
       (IF isMulti THEN <<"(", "\\E", "self", "\\in", "ProcSet", ":">> ELSE <<>>) \o
       GenerateActionDisj(labels, isMulti, "") \o
       (IF isMulti THEN <<")">> ELSE <<>>) \o
       <<"\\/">> \o <<"(* Disjunct to prevent deadlock on termination *)", Newline>> \o
       <<"(", "(", "\\A", "self", "\\in", "ProcSet", ":", 
        "pc", "[", "self", "]", "=", "\"Done\"", ")">> \o
       <<"/\\", "UNCHANGED", "vars", ")">> \o
       <<Newline, Newline>>

(* Generate Spec with fairness *)
TranslateSpec(alg, fairnessOption) ==
    LET isMulti == IsMultiprocess(alg)
        base == <<"Spec", "==", "Init", "/\\", "[]", "[", "Next", "]", "_", "vars">>
        fairness == CASE fairnessOption = NoFairness -> <<>>
                      [] fairnessOption = WeakFairnessNext -> <<"/\\", "WF_", "vars", "(", "Next", ")">>
                      [] fairnessOption = WeakFairnessAll -> 
                         IF isMulti 
                         THEN <<"/\\", "\\A", "self", "\\in", "ProcSet", ":", "WF_", "vars", "(", "Next", ")">>
                         ELSE <<"/\\", "WF_", "vars", "(", "Next", ")">>
                      [] fairnessOption = StrongFairnessAll ->
                         IF isMulti 
                         THEN <<"/\\", "\\A", "self", "\\in", "ProcSet", ":", "SF_", "vars", "(", "Next", ")">>
                         ELSE <<"/\\", "SF_", "vars", "(", "Next", ")">>
                      [] OTHER -> <<>>
    IN base \o fairness \o <<Newline, Newline>>

(* Generate Termination property *)
TranslateTermination(alg) ==
    LET isMulti == IsMultiprocess(alg)
    IN <<"Termination", "==", "<>", "(">> \o
       (IF isMulti 
        THEN <<"\\A", "self", "\\in", "ProcSet", ":", "pc", "[", "self", "]", "=", "\"Done\"">>
        ELSE <<"pc", "=", "\"Done\"">>
       ) \o
       <<")", Newline, Newline>>

(* Generate variables declaration *)
TranslateVarsDecl(alg) ==
    LET globalVarNames == ExtractVarNames(alg.vars)
        hasStack == alg.procs # <<>>
        allVars == globalVarNames \cup {"pc"} \cup (IF hasStack THEN {"stack"} ELSE {})
    IN <<"VARIABLES">> \o 
       [i \in 1..Cardinality(allVars) |-> 
           LET v == CHOOSE x \in allVars : TRUE IN <<v, ",">>
       ] \o
       <<Newline, Newline>> \o
       <<"vars", "==", "<<">> \o
       [i \in 1..Cardinality(allVars) |-> 
           LET v == CHOOSE x \in allVars : TRUE IN <<v, ",">>
       ] \o
       <<">>">> \o
       <<Newline, Newline>>

(* Generate ProcSet definition for multiprocess *)
TranslateProcSetDef(alg) ==
    IF ~IsMultiprocess(alg) THEN <<>>
    ELSE <<"ProcSet", "==">> \o TranslateProcSet(alg.processes) \o <<Newline, Newline>>

(* Main Translation operator *)
Translation(alg, fairnessOption) ==
    LET isMulti == IsMultiprocess(alg)
        header == <<"----", "MODULE", alg.name, "----", Newline>>
        extends == <<"EXTENDS", "Naturals", ",", "Sequences", ",", "TLC", Newline, Newline>>
        varsDecl == TranslateVarsDecl(alg)
        procSetDef == TranslateProcSetDef(alg)
        procedures == TranslateProcedures(alg.procs, isMulti)
        body == IF isMulti 
                THEN TranslateProcesses(alg.processes)
                ELSE TranslateLabeledStmts(alg.body, 1, FALSE, "")
        initDef == TranslateInit(alg)
        nextDef == TranslateNext(alg)
        specDef == TranslateSpec(alg, fairnessOption)
        termination == TranslateTermination(alg)
        footer == <<"====