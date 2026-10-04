---------------------------- MODULE PlusCalTranslation ----------------------------
EXTENDS Sequences, Integers, TLC, FiniteSets

CONSTANTS
    \* AST Node Types
    AlgorithmNode, ProcedureNode, ProcessNode, LabeledStmtNode,
    AssignNode, IfNode, WhileNode, CallNode, ReturnNode, GotoNode,
    PrintNode, AssertNode, SkipNode, WithNode, AwaitNode,
    \* Fairness options
    NoFairness, WeakFairnessProcess, WeakFairnessNext, StrongFairnessProcess,
    \* Special constants
    Nil, Done,
    \* Maximum sizes for model checking
    MaxVars, MaxProcs, MaxStmts, MaxLabels

VARIABLES
    \* The input AST
    ast,
    \* Current translation state
    translationState,
    \* Generated TLA+ output (sequence of lexemes)
    output,
    \* Symbol table for variables, procedures, processes
    symbolTable,
    \* Current fairness option
    fairnessOption,
    \* Error state
    errorState,
    \* Program counter mapping
    pcMapping

vars == <<ast, translationState, output, symbolTable, fairnessOption, errorState, pcMapping>>

-----------------------------------------------------------------------------
\* Type definitions for AST nodes (represented as records)

IsIdentifier(id) == id \in STRING

IsExpr(e) == 
    \/ e \in STRING
    \/ (DOMAIN e = {"op", "args"} /\ e.op \in STRING /\ e.args \in Seq(STRING))

IsVarDecl(v) ==
    /\ DOMAIN v = {"name", "init", "type"}
    /\ IsIdentifier(v.name)
    /\ IsExpr(v.init)

IsAssignment(a) ==
    /\ DOMAIN a = {"nodeType", "lhs", "rhs"}
    /\ a.nodeType = AssignNode
    /\ IsIdentifier(a.lhs)
    /\ IsExpr(a.rhs)

IsStatement(s) ==
    /\ "nodeType" \in DOMAIN s
    /\ s.nodeType \in {AssignNode, IfNode, WhileNode, CallNode, ReturnNode, 
                       GotoNode, PrintNode, AssertNode, SkipNode, WithNode, AwaitNode}

IsLabeledStmt(ls) ==
    /\ DOMAIN ls = {"nodeType", "label", "stmts"}
    /\ ls.nodeType = LabeledStmtNode
    /\ IsIdentifier(ls.label)
    /\ ls.stmts \in Seq(BOOLEAN)  \* Seq of statements

IsProcedure(p) ==
    /\ DOMAIN p = {"nodeType", "name", "params", "locals", "body"}
    /\ p.nodeType = ProcedureNode
    /\ IsIdentifier(p.name)
    /\ p.params \in Seq(BOOLEAN)  \* Seq of param decls
    /\ p.locals \in Seq(BOOLEAN)  \* Seq of var decls
    /\ p.body \in Seq(BOOLEAN)    \* Seq of labeled statements

IsProcess(pr) ==
    /\ DOMAIN pr = {"nodeType", "name", "id", "locals", "body", "fair"}
    /\ pr.nodeType = ProcessNode
    /\ IsIdentifier(pr.name)
    /\ pr.locals \in Seq(BOOLEAN)
    /\ pr.body \in Seq(BOOLEAN)
    /\ pr.fair \in {NoFairness, WeakFairnessProcess, StrongFairnessProcess}

IsAlgorithm(alg) ==
    /\ DOMAIN alg = {"nodeType", "name", "globals", "procedures", "processes", "fair"}
    /\ alg.nodeType = AlgorithmNode
    /\ IsIdentifier(alg.name)
    /\ alg.globals \in Seq(BOOLEAN)     \* Seq of var decls
    /\ alg.procedures \in Seq(BOOLEAN)  \* Seq of procedures
    /\ alg.processes \in Seq(BOOLEAN)   \* Seq of processes
    /\ alg.fair \in {NoFairness, WeakFairnessProcess, WeakFairnessNext, StrongFairnessProcess}

-----------------------------------------------------------------------------
\* Lexeme types for output

Lexeme(type, value) == [type |-> type, value |-> value]

Keyword(k) == Lexeme("keyword", k)
Ident(i) == Lexeme("ident", i)
Op(o) == Lexeme("op", o)
Literal(l) == Lexeme("literal", l)
Newline == Lexeme("newline", "")
Indent(n) == Lexeme("indent", n)

-----------------------------------------------------------------------------
\* Translation state machine

TranslationStates == {"idle", "parsing", "translatingVars", "translatingInit", 
                      "translatingActions", "translatingNext", "translatingSpec",
                      "translatingFairness", "translatingTermination", "done", "error"}

-----------------------------------------------------------------------------
\* Helper operators for generating TLA+ constructs

\* Generate variable declarations
TranslateVarDecls(decls) ==
    IF decls = <<>> THEN <<>>
    ELSE LET d == Head(decls)
         IN <<Ident(d.name)>> \o 
            (IF d.init # Nil THEN <<Op("="), Literal(d.init)>> ELSE <<>>) \o
            <<Newline>> \o
            TranslateVarDecls(Tail(decls))

\* Generate the VARIABLES section
GenerateVariablesSection(globals, procs, processes) ==
    <<Keyword("VARIABLES"), Newline>> \o
    <<Ident("pc")>> \o
    (IF procs # <<>> THEN <<Op(","), Ident("stack")>> ELSE <<>>) \o
    <<Newline>>

\* Generate Init predicate
GenerateInit(alg) ==
    <<Ident("Init"), Op("=="), Newline, Indent(2)>> \o
    <<Op("/\\"), Ident("pc"), Op("=")>> \o
    (IF alg.processes = <<>> 
     THEN <<Literal("\"start\"")>>
     ELSE <<Op("["), Ident("self"), Op("\\in"), Ident("ProcSet"), 
            Op("|->"), Literal("\"start\""), Op("]")>>) \o
    <<Newline>>

\* Generate a single action for a labeled statement
GenerateAction(procName, label, stmt) ==
    <<Ident(procName \o "_" \o label), Op("=="), Newline, Indent(2)>> \o
    <<Op("/\\"), Ident("pc"), Op("="), Literal("\"" \o label \o "\""), Newline>> \o
    <<Indent(2), Op("/\\"), Ident("pc'"), Op("=")>>

\* Generate Next predicate
GenerateNext(alg) ==
    <<Ident("Next"), Op("=="), Newline, Indent(2)>> \o
    <<Op("\\/"), Ident("Terminating")>> \o
    <<Newline>>

\* Generate Spec with fairness
GenerateSpec(alg) ==
    LET baseDef == <<Ident("Spec"), Op("=="), Ident("Init"), Op("/\\"), 
                     Op("[]"), Op("["), Ident("Next"), Op("]_"), Ident("vars")>>
        fairPart == CASE alg.fair = NoFairness -> <<>>
                      [] alg.fair = WeakFairnessNext -> 
                         <<Op("/\\"), Keyword("WF_"), Ident("vars"), 
                           Op("("), Ident("Next"), Op(")")>>
                      [] alg.fair = WeakFairnessProcess ->
                         <<Op("/\\"), Ident("Fairness")>>
                      [] alg.fair = StrongFairnessProcess ->
                         <<Op("/\\"), Ident("Fairness")>>
                      [] OTHER -> <<>>
    IN baseDef \o fairPart \o <<Newline>>

\* Generate Termination property
GenerateTermination(alg) ==
    <<Ident("Termination"), Op("=="), Op("<>"), Op("(")>> \o
    (IF alg.processes = <<>>
     THEN <<Ident("pc"), Op("="), Literal("\"Done\"")>>
     ELSE <<Op("\\A"), Ident("self"), Op("\\in"), Ident("ProcSet"), 
            Op(":"), Ident("pc"), Op("["), Ident("self"), Op("]"), 
            Op("="), Literal("\"Done\"")>>) \o
    <<Op(")"), Newline>>

\* Generate Fairness conditions
GenerateFairness(alg) ==
    CASE alg.fair = NoFairness -> <<>>
      [] alg.fair = WeakFairnessProcess ->
         <<Ident("Fairness"), Op("=="), Newline, Indent(2)>> \o
         <<Op("\\A"), Ident("self"), Op("\\in"), Ident("ProcSet"), Op(":"),
           Keyword("WF_"), Ident("vars"), Op("("), Ident("proc"), 
           Op("("), Ident("self"), Op(")"), Op(")"), Newline>>
      [] alg.fair = StrongFairnessProcess ->
         <<Ident("Fairness"), Op("=="), Newline, Indent(2)>> \o
         <<Op("\\A"), Ident("self"), Op("\\in"), Ident("ProcSet"), Op(":"),
           Keyword("SF_"), Ident("vars"), Op("("), Ident("proc"),
           Op("("), Ident("self"), Op(")"), Op(")"), Newline>>
      [] OTHER -> <<>>

-----------------------------------------------------------------------------
\* Main translation operator

TranslateAlgorithm(alg) ==
    IF ~(DOMAIN alg = {"nodeType", "name", "globals", "procedures", "processes", "fair"})
    THEN [error |-> "Invalid algorithm structure", output |-> <<>>]
    ELSE
        LET header == <<Keyword("----"), Keyword("MODULE"), Ident(alg.name), 
                        Keyword("----"), Newline>>
            extends == <<Keyword("EXTENDS"), Ident("Naturals"), Op(","), 
                         Ident("Sequences"), Op(","), Ident("TLC"), Newline>>
            varsSection == GenerateVariablesSection(alg.globals, alg.procedures, alg.processes)
            initSection == GenerateInit(alg)
            nextSection == GenerateNext(alg)
            specSection == GenerateSpec(alg)
            termSection == GenerateTermination(alg)
            fairSection == GenerateFairness(alg)
            footer == <<Keyword("====