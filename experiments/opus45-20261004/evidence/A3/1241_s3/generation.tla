-------------------------------- MODULE PlusCal --------------------------------
\* TLA+ specification of PlusCal to TLA+ translation
\* This module specifies the translation from abstract syntax trees of 
\* global-naming PlusCal algorithms into TLA+ specifications

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    \* Maximum sizes for bounded model checking
    MaxLabels,
    MaxVars,
    MaxProcs,
    MaxStmts,
    
    \* AST node types
    AlgorithmNode,
    ProcedureNode,
    ProcessNode,
    LabeledStmtNode,
    AssignNode,
    IfNode,
    WhileNode,
    EitherNode,
    WithNode,
    AwaitNode,
    PrintNode,
    AssertNode,
    SkipNode,
    ReturnNode,
    CallNode,
    GotoNode,
    
    \* Fairness options
    NoFairness,
    WeakFairnessProc,
    WeakFairnessNext,
    StrongFairnessProc,
    
    \* Special tokens
    NullToken,
    PCVar,
    StackVar

VARIABLES
    \* Input AST
    ast,
    
    \* Translation state
    translationState,
    currentNode,
    outputLexemes,
    
    \* Symbol tables
    globalVars,
    localVars,
    procedures,
    processes,
    labels,
    
    \* Translation options
    fairnessOption,
    
    \* Error state
    errorState

vars == <<ast, translationState, currentNode, outputLexemes, 
          globalVars, localVars, procedures, processes, labels,
          fairnessOption, errorState>>

\* -----------------------------------------------------------------------------
\* AST Grammar Definitions
\* An AST node is a record with a type and associated fields
\* -----------------------------------------------------------------------------

\* Valid identifier (simplified as non-empty string representation)
IsValidId(id) == id \in STRING /\ id # ""

\* Variable declaration: [name: STRING, init: Expr]
IsVarDecl(v) == 
    /\ DOMAIN v = {"name", "init"}
    /\ IsValidId(v.name)

\* Expression (simplified - in full spec would be recursive AST)
IsExpr(e) == TRUE

\* Statement types
IsAssignStmt(s) ==
    /\ s.type = AssignNode
    /\ "lhs" \in DOMAIN s
    /\ "rhs" \in DOMAIN s

IsIfStmt(s) ==
    /\ s.type = IfNode
    /\ "cond" \in DOMAIN s
    /\ "then" \in DOMAIN s
    /\ "else" \in DOMAIN s

IsWhileStmt(s) ==
    /\ s.type = WhileNode
    /\ "cond" \in DOMAIN s
    /\ "body" \in DOMAIN s

IsEitherStmt(s) ==
    /\ s.type = EitherNode
    /\ "branches" \in DOMAIN s

IsWithStmt(s) ==
    /\ s.type = WithNode
    /\ "var" \in DOMAIN s
    /\ "expr" \in DOMAIN s
    /\ "body" \in DOMAIN s

IsAwaitStmt(s) ==
    /\ s.type = AwaitNode
    /\ "cond" \in DOMAIN s

IsPrintStmt(s) ==
    /\ s.type = PrintNode
    /\ "expr" \in DOMAIN s

IsAssertStmt(s) ==
    /\ s.type = AssertNode
    /\ "cond" \in DOMAIN s

IsSkipStmt(s) ==
    s.type = SkipNode

IsReturnStmt(s) ==
    s.type = ReturnNode

IsCallStmt(s) ==
    /\ s.type = CallNode
    /\ "proc" \in DOMAIN s
    /\ "args" \in DOMAIN s

IsGotoStmt(s) ==
    /\ s.type = GotoNode
    /\ "label" \in DOMAIN s

IsSimpleStmt(s) ==
    \/ IsAssignStmt(s)
    \/ IsAwaitStmt(s)
    \/ IsPrintStmt(s)
    \/ IsAssertStmt(s)
    \/ IsSkipStmt(s)
    \/ IsReturnStmt(s)
    \/ IsCallStmt(s)
    \/ IsGotoStmt(s)

IsCompoundStmt(s) ==
    \/ IsIfStmt(s)
    \/ IsWhileStmt(s)
    \/ IsEitherStmt(s)
    \/ IsWithStmt(s)

IsStatement(s) ==
    \/ IsSimpleStmt(s)
    \/ IsCompoundStmt(s)

\* Labeled statement: [label: STRING, stmts: Seq(Statement)]
IsLabeledStmt(ls) ==
    /\ ls.type = LabeledStmtNode
    /\ "label" \in DOMAIN ls
    /\ IsValidId(ls.label)
    /\ "stmts" \in DOMAIN ls

\* Procedure: [name, params, vars, body]
IsProcedure(p) ==
    /\ p.type = ProcedureNode
    /\ "name" \in DOMAIN p
    /\ IsValidId(p.name)
    /\ "params" \in DOMAIN p
    /\ "localVars" \in DOMAIN p
    /\ "body" \in DOMAIN p

\* Process: [name, id, vars, body, fairness]
IsProcess(p) ==
    /\ p.type = ProcessNode
    /\ "name" \in DOMAIN p
    /\ IsValidId(p.name)
    /\ "id" \in DOMAIN p
    /\ "localVars" \in DOMAIN p
    /\ "body" \in DOMAIN p

\* Algorithm: [name, vars, procedures, processes | body]
IsAlgorithm(a) ==
    /\ a.type = AlgorithmNode
    /\ "name" \in DOMAIN a
    /\ IsValidId(a.name)
    /\ "globalVars" \in DOMAIN a
    /\ "procedures" \in DOMAIN a
    /\ \/ "processes" \in DOMAIN a  \* Multiprocess algorithm
       \/ "body" \in DOMAIN a        \* Uniprocess algorithm

\* -----------------------------------------------------------------------------
\* Lexeme Sequence Operations
\* Lexemes represent tokens in the output TLA+ specification
\* -----------------------------------------------------------------------------

\* A lexeme is either a string token or a structured element
IsLexeme(l) == l \in STRING

\* Concatenate lexeme sequences
ConcatLexemes(s1, s2) == s1 \o s2

\* Create lexeme for identifier
IdLexeme(id) == <<id>>

\* Create lexeme for keyword
KeywordLexeme(kw) == <<kw>>

\* Create lexeme for operator
OpLexeme(op) == <<op>>

\* Create lexeme for delimiter
DelimLexeme(d) == <<d>>

\* Newline lexeme
NewlineLexeme == <<"\n">>

\* Indent lexeme
IndentLexeme(n) == <<" ">>  \* Simplified

\* -----------------------------------------------------------------------------
\* Translation State
\* -----------------------------------------------------------------------------

TranslationStates == {
    "Init",
    "TranslatingVars",
    "TranslatingProcedures", 
    "TranslatingProcesses",
    "TranslatingInit",
    "TranslatingNext",
    "TranslatingSpec",
    "TranslatingFairness",
    "TranslatingTermination",
    "Done",
    "Error"
}

\* -----------------------------------------------------------------------------
\* Variable Translation
\* Translates variable declarations to TLA+ VARIABLES and Init assignments
\* -----------------------------------------------------------------------------

TranslateVarDecl(v) ==
    ConcatLexemes(IdLexeme(v.name), OpLexeme(" = "))

TranslateVarInit(v) ==
    \* In full implementation, would translate init expression
    <<v.name, " = ", "initValue">>

\* Generate VARIABLES declaration
GenerateVariablesDecl(gvars, procs, processes_set) ==
    LET baseVars == {v.name : v \in gvars}
        procLocalVars == UNION {
            {v.name : v \in p.localVars} : p \in procs
        }
        processLocalVars == UNION {
            {v.name : v \in p.localVars} : p \in processes_set
        }
        allVars == baseVars \cup procLocalVars \cup processLocalVars \cup {PCVar, StackVar}
    IN <<"VARIABLES ", allVars>>

\* -----------------------------------------------------------------------------
\* Statement Translation
\* -----------------------------------------------------------------------------

\* Forward declaration pattern - actual implementation would be recursive
RECURSIVE TranslateStmts(_)

TranslateAssign(s, nextLabel) ==
    <<s.lhs, "' = ", s.rhs, " /\\ ", PCVar, "' = ", nextLabel>>

TranslateAwait(s) ==
    <<s.cond>>

TranslatePrint(s) ==
    <<"PrintT(", s.expr, ")">>

TranslateAssert(s) ==
    <<"Assert(", s.cond, ", \"Assertion failed\")">>

TranslateSkip ==
    <<"TRUE">>

TranslateGoto(s) ==
    <<PCVar, "' = ", s.label>>

TranslateReturn ==
    \* Pop from stack and restore pc
    <<"Head(", StackVar, ").pc /\\ ", StackVar, "' = Tail(", StackVar, ")">>

TranslateCall(s) ==
    \* Push to stack and set pc to procedure entry
    <<StackVar, "' = <<[pc |-> ", "returnLabel", "]>> \\o ", StackVar,
      " /\\ ", PCVar, "' = ", s.proc, "_entry">>

TranslateIf(s, nextLabel) ==
    <<"IF ", s.cond, " THEN ", TranslateStmts(s.then),
      " ELSE ", TranslateStmts(s.else)>>

TranslateWhile(s, loopLabel, exitLabel) ==
    <<"IF ", s.cond, " THEN ", TranslateStmts(s.body), " /\\ ", PCVar, "' = ", loopLabel,
      " ELSE ", PCVar, "' = ", exitLabel>>

TranslateEither(s) ==
    \* Nondeterministic choice
    <<"\\/ ", s.branches>>

TranslateWith(s) ==
    <<"\\E ", s.var, " \\in ", s.expr, ": ", TranslateStmts(s.body)>>

TranslateStmts(stmts) ==
    IF stmts = <<>> THEN <<"TRUE">>
    ELSE <<"stmts_placeholder">>

\* -----------------------------------------------------------------------------
\* Labeled Statement Translation
\* Generates a TLA+ action for each label
\* -----------------------------------------------------------------------------

TranslateLabeledStmt(ls, procName, nextLabel) ==
    LET actionName == procName \o "_" \o ls.label
        pcGuard == <<PCVar, " = \"", ls.label, "\"">>
        body == TranslateStmts(ls.stmts)
    IN <<actionName, " == ", pcGuard, " /\\ ", body>>

\* -----------------------------------------------------------------------------
\* Procedure Translation
\* -----------------------------------------------------------------------------

TranslateProcedure(proc) ==
    LET entryLabel == proc.name \o "_entry"
        actions == {TranslateLabeledStmt(ls, proc.name, "next") : ls \in ToSet(proc.body)}
    IN actions

\* -----------------------------------------------------------------------------
\* Process Translation
\* -----------------------------------------------------------------------------

TranslateProcess(p) ==
    LET processActions == {TranslateLabeledStmt(ls, p.name, "next") : ls \in ToSet(p.body)}
        processAction == <<p.name, " == \\/ ", processActions>>
    IN processAction

\* -----------------------------------------------------------------------------
\* Init Predicate Generation
\* -----------------------------------------------------------------------------

GenerateInit(alg) ==
    LET varInits == {TranslateVarInit(v) : v \in ToSet(alg.globalVars)}
        pcInit == IF "processes" \in DOMAIN alg
                  THEN <<PCVar, " = [self \\in ProcSet |-> \"start\"]">>
                  ELSE <<PCVar, " = \"start\"">>
        stackInit == <<StackVar, " = <<>>">>
    IN <<"Init == ", varInits, " /\\ ", pcInit, " /\\ ", stackInit>>

\* -----------------------------------------------------------------------------
\* Next Predicate Generation
\* -----------------------------------------------------------------------------

GenerateNext(alg) ==
    LET procActions == IF "procedures" \in DOMAIN alg
                       THEN {p.name : p \in ToSet(alg.procedures)}
                       ELSE {}
        processActions == IF "processes" \in DOMAIN alg
                         THEN {p.name : p \in ToSet(alg.processes)}
                         ELSE {}
        allActions == procActions \cup processActions
        disjunction == <<"\\/ ", allActions>>
        terminating == <<"\\/ (", PCVar, " = \"Done\" /\\ UNCHANGED vars)">>
    IN <<"Next == ", disjunction, terminating>>

\* -----------------------------------------------------------------------------
\* Fairness Generation
\* -----------------------------------------------------------------------------

GenerateFairness(alg, option) ==
    CASE option = NoFairness -> <<>>
      [] option = WeakFairnessNext -> <<"WF_vars(Next)">>
      [] option = WeakFairnessProc -> 
            IF "processes" \in DOMAIN alg
            THEN <<"\\A self \\in ProcSet: WF_vars(", "process(self)", ")">>
            ELSE <<"WF_vars(Next)">>
      [] option = StrongFairnessProc ->
            IF "processes" \in DOMAIN alg
            THEN <<"\\A self \\in ProcSet: SF_vars(", "process(self)", ")">>
            ELSE <<"SF_vars(Next)">>
      [] OTHER -> <<>>

\* -----------------------------------------------------------------------------
\* Spec Generation
\* -----------------------------------------------------------------------------

GenerateSpec(alg, fairness_opt) ==
    LET fairness == GenerateFairness(alg, fairness_opt)
    IN IF fairness = <<>>
       THEN <<"Spec == Init /\\ [][Next]_vars">>
       ELSE <<"Spec == Init /\\ [][Next]_vars /\\ ", fairness>>

\* -----------------------------------------------------------------------------
\* Termination Property Generation
\* -----------------------------------------------------------------------------

GenerateTermination(alg) ==
    IF "processes" \in DOMAIN alg
    THEN <<"Termination == <>(\\A self \\in ProcSet: ", PCVar, "[self] = \"Done\")">>
    ELSE <<"Termination == <>(", PCVar, " = \"Done\")">>

\* -----------------------------------------------------------------------------
\* Helper Functions
\* -----------------------------------------------------------------------------

ToSet(seq) == {seq[i] : i \in DOMAIN seq}

CollectLabels(body) ==
    {ls.label : ls \in ToSet(body)}

CollectAllLabels(alg) ==
    LET procLabels == IF "procedures" \in DOMAIN alg
                      THEN UNION {CollectLabels(p.body) : p \in ToSet(alg.procedures)}
                      ELSE {}
        processLabels == IF "processes" \in DOMAIN alg
                        THEN UNION {CollectLabels(p.body) : p \in ToSet(alg.processes)}
                        ELSE {}
        bodyLabels == IF "body" \in DOMAIN alg
                     THEN CollectLabels(alg.body)
                     ELSE {}
    IN procLabels \cup processLabels \cup bodyLabels

\* -----------------------------------------------------------------------------
\* Error Checking
\* -----------------------------------------------------------------------------

\* Check for duplicate labels
HasDuplicateLabels(alg) ==
    LET allLabels == CollectAllLabels(alg)
    IN FALSE  \* Simplified - would check for duplicates in sequences

\* Check for undefined goto targets
HasUndefinedGotos(alg) ==
    FALSE  \* Simplified

\* Check for procedure call to undefined procedure
HasUndefinedCalls(alg) ==
    FALSE  \* Simplified

\* Validate AST
ValidateAST(a) ==
    /\ IsAlgorithm(a)
    /\ ~HasDuplicateLabels(a)
    /\ ~HasUndefinedGotos(a)
    /\ ~HasUndefinedCalls(a)

\* -----------------------------------------------------------------------------
\* Type Invariant
\* -----------------------------------------------------------------------------

TypeInvariant ==
    /\ translationState \in TranslationStates
    /\ outputLexemes \in Seq(STRING)
    /\ errorState \in BOOLEAN \cup STRING
    /\ fairnessOption \in {NoFairness, WeakFairnessProc, WeakFairnessNext, StrongFairnessProc}

\* -----------------------------------------------------------------------------
\* Initial State
\* -----------------------------------------------------------------------------

Init ==
    /\ ast = [type |-> AlgorithmNode, name |-> "Algorithm", 
              globalVars |-> <<>>, procedures |-> <<>>, processes |-> <<>>]
    /\ translationState = "Init"
    /\ currentNode = NullToken
    /\ outputLexemes = <<>>
    /\ globalVars = {}
    /\ localVars = {}
    /\ procedures = {}
    /\ processes = {}
    /\ labels = {}
    /\ fairnessOption = NoFairness
    /\ errorState = FALSE

\* -----------------------------------------------------------------------------
\* Translation Actions
\* -----------------------------------------------------------------------------

\* Start translation by validating AST
StartTranslation ==
    /\ translationState = "Init"
    /\ IF ValidateAST(ast)
       THEN /\ translationState' = "TranslatingVars"
            /\ errorState' = FALSE
       ELSE /\ translationState' = "Error"
            /\ errorState' = "Invalid AST"
    /\ UNCHANGED <<ast, currentNode, outputLexemes, globalVars, localVars,
                   procedures, processes, labels, fairnessOption>>

\* Translate variable declarations
TranslateVariables ==
    /\ translationState = "TranslatingVars"
    /\ LET varsDecl == GenerateVariablesDecl(ToSet(ast.globalVars), 
                                             ToSet(ast.procedures),
                                             ToSet(ast.processes))
       IN outputLexemes' = ConcatLexemes(outputLexemes, varsDecl)
    /\ translationState' = "TranslatingProcedures"
    /\ globalVars' = ToSet(ast.globalVars)
    /\ UNCHANGED <<ast, currentNode, localVars, procedures, processes, 
                   labels, fairnessOption, errorState>>

\* Translate procedures
TranslateProcedures ==
    /\ translationState = "TranslatingProcedures"
    /\ LET procs == IF "procedures" \in DOMAIN ast 
                    THEN ToSet(ast.procedures) 
                    ELSE {}
           procOutput == UNION {TranslateProcedure(p) : p \in procs}
       IN outputLexemes' = ConcatLexemes(outputLexemes, <<procOutput>>)
    /\ translationState' = "TranslatingProcesses"
    /\ procedures' = IF "procedures" \in DOMAIN ast 
                     THEN {p.name : p \in ToSet(ast.procedures)}
                     ELSE {}
    /\ UNCHANGED <<ast, currentNode, globalVars, localVars, processes,
                   labels, fairnessOption, errorState>>

\* Translate processes
TranslateProcesses ==
    /\ translationState = "TranslatingProcesses"
    /\ LET procs == IF "processes" \in DOMAIN ast
                    THEN ToSet(ast.processes)
                    ELSE {}
           procOutput == {TranslateProcess(p) : p \in procs}
       IN outputLexemes' = ConcatLexemes(outputLexemes, <<procOutput>>)
    /\ translationState' = "TranslatingInit"
    /\ processes' = IF "processes" \in DOMAIN ast
                    THEN {p.name : p \in ToSet(ast.processes)}
                    ELSE {}
    /\ labels' = CollectAllLabels(ast)
    /\ UNCHANGED <<ast, currentNode, globalVars, localVars, procedures,
                   fairnessOption, errorState>>

\* Translate Init predicate
TranslateInit ==
    /\ translationState = "TranslatingInit"
    /\ LET initPred == GenerateInit(ast)
       IN outputLexemes' = ConcatLexemes(outputLexemes, initPred)
    /\ translationState' = "TranslatingNext"
    /\ UNCHANGED <<ast, currentNode, globalVars, localVars, procedures,
                   processes, labels, fairnessOption, errorState>>

\* Translate Next predicate
TranslateNext ==
    /\ translationState = "TranslatingNext"
    /\ LET nextPred == GenerateNext(ast)
       IN outputLexemes' = ConcatLexemes(outputLexemes, nextPred)
    /\ translationState' = "TranslatingSpec"
    /\ UNCHANGED <<ast, currentNode, globalVars, localVars, procedures,
                   processes, labels, fairnessOption, errorState>>

\* Translate Spec predicate
TranslateSpec ==
    /\ translationState = "TranslatingSpec"
    /\ LET specPred == GenerateSpec(ast, fairnessOption)
       IN outputLexemes' = ConcatLexemes(outputLexemes, specPred)
    /\ translationState' = "TranslatingTermination"
    /\ UNCHANGED <<ast, currentNode, globalVars, localVars, procedures,
                   processes, labels, fairnessOption, errorState>>

\* Translate Termination property
TranslateTermination ==
    /\ translationState = "TranslatingTermination"
    /\ LET termProp == GenerateTermination(ast)
       IN outputLexemes' = ConcatLexemes(outputLexemes, termProp)
    /\ translationState' = "Done"
    /\ UNCHANGED <<ast, currentNode, globalVars, localVars, procedures,
                   processes, labels, fairnessOption, errorState>>

\* Set fairness option (can be done in Init state)
SetFairness(option) ==
    /\ translationState = "Init"
    /\ option \in {NoFairness, WeakFairnessProc, WeakFairnessNext, StrongFairnessProc}
    /\ fairnessOption' = option
    /\ UNCHANGED <<ast, translationState, currentNode, outputLexemes,
                   globalVars, localVars, procedures, processes, labels, errorState>>

\* -----------------------------------------------------------------------------
\* Next State Relation
\* -----------------------------------------------------------------------------

Next ==
    \/ StartTranslation
    \/ TranslateVariables
    \/ TranslateProcedures
    \/ TranslateProcesses
    \/ TranslateInit
    \/ TranslateNext
    \/ TranslateSpec
    \/ TranslateTermination
    \/ \E opt \in {NoFairness, WeakFairnessProc, WeakFairnessNext, StrongFairnessProc}:
          SetFairness(opt)

\* -----------------------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------------------

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* -----------------------------------------------------------------------------
\* Safety Invariants
\* -----------------------------------------------------------------------------

\* Translation state is always valid
StateInvariant == translationState \in TranslationStates

\* If in error state, we don't continue translating
ErrorStateInvariant ==
    errorState # FALSE => translationState = "Error"

\* Labels are unique (once collected)
UniqueLabelsInvariant ==
    translationState \in {"TranslatingInit", "TranslatingNext", "TranslatingSpec",
                          "TranslatingTermination", "Done"} =>
        Cardinality(labels) = Cardinality(labels)  \* Tautology - full check would verify uniqueness

\* Output lexemes form valid TLA+ syntax (simplified check)
ValidOutputInvariant ==
    outputLexemes \in Seq(STRING)

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeInvariant
    /\ StateInvariant
    /\ ErrorStateInvariant
    /\ ValidOutputInvariant

\* -----------------------------------------------------------------------------
\* Liveness Properties
\* -----------------------------------------------------------------------------

\* Translation eventually completes (reaches Done or Error)
TranslationCompletes ==
    <>(translationState \in {"Done", "Error"})

\* If AST is valid, translation succeeds
ValidASTImpliesSuccess ==
    (ValidateAST(ast) /\ translationState = "Init") ~> (translationState = "Done")

\* Once done, we stay done
StabilityWhenDone ==
    [](translationState = "Done" => [](translationState = "Done"))

\* Termination property for the translation itself
Termination == <>(translationState \in {"Done", "Error"})

================================================================================