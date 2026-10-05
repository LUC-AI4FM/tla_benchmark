---------------------------- MODULE PlusCalToTLA ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    \* AST Node Types
    VarDecl, Assignment, If, While, Either, With, Await, Print, Assert,
    Skip, Return, Call, Goto, LabeledStmt, Procedure, Process, Algorithm,
    
    \* Expression Types
    Identifier, IntLit, StringLit, BoolLit, BinOp, UnaryOp, FuncApp,
    
    \* Fairness Options
    NoFairness, WeakFairProcess, WeakFairNext, StrongFairProcess,
    
    \* Maximum values for bounded model checking
    MaxProcs, MaxVars, MaxStmts, MaxLabels

VARIABLES
    \* Input AST
    ast,
    
    \* Translation state
    translationPhase,
    explodedStmts,
    translatedStmts,
    subscriptedVars,
    
    \* Output TLA+ components
    tlaPlusInit,
    tlaPlusNext,
    tlaPlusSpec,
    tlaPlusTermination,
    tlaPlusFairness,
    
    \* Process tracking
    processSet,
    procedureSet,
    globalVars,
    localVars,
    pcVar,
    stackVar,
    
    \* Error state
    translationError

vars == <<ast, translationPhase, explodedStmts, translatedStmts, 
          subscriptedVars, tlaPlusInit, tlaPlusNext, tlaPlusSpec,
          tlaPlusTermination, tlaPlusFairness, processSet, procedureSet,
          globalVars, localVars, pcVar, stackVar, translationError>>

-----------------------------------------------------------------------------
(* AST Grammar Definitions as Sets and Predicates *)

\* Check if a record is a valid expression
IsExpr(e) ==
    /\ e \in [type: {Identifier, IntLit, StringLit, BoolLit, BinOp, UnaryOp, FuncApp}]
    /\ CASE e.type = Identifier -> "name" \in DOMAIN e
         [] e.type = IntLit -> "value" \in DOMAIN e
         [] e.type = StringLit -> "value" \in DOMAIN e
         [] e.type = BoolLit -> "value" \in DOMAIN e
         [] e.type = BinOp -> /\ "op" \in DOMAIN e 
                              /\ "left" \in DOMAIN e 
                              /\ "right" \in DOMAIN e
         [] e.type = UnaryOp -> /\ "op" \in DOMAIN e 
                                /\ "operand" \in DOMAIN e
         [] e.type = FuncApp -> /\ "func" \in DOMAIN e 
                                /\ "args" \in DOMAIN e
         [] OTHER -> FALSE

\* Check if a record is a valid variable declaration
IsVarDecl(v) ==
    /\ v \in [type: {VarDecl}]
    /\ "name" \in DOMAIN v
    /\ "initValue" \in DOMAIN v

\* Check if a record is a valid statement
RECURSIVE IsStmt(_)
IsStmt(s) ==
    /\ s \in [type: {Assignment, If, While, Either, With, Await, Print, 
                     Assert, Skip, Return, Call, Goto, LabeledStmt}]
    /\ CASE s.type = Assignment -> /\ "lhs" \in DOMAIN s 
                                   /\ "rhs" \in DOMAIN s
         [] s.type = If -> /\ "condition" \in DOMAIN s 
                           /\ "thenBranch" \in DOMAIN s 
                           /\ "elseBranch" \in DOMAIN s
         [] s.type = While -> /\ "condition" \in DOMAIN s 
                              /\ "body" \in DOMAIN s
         [] s.type = Either -> "branches" \in DOMAIN s
         [] s.type = With -> /\ "var" \in DOMAIN s 
                             /\ "set" \in DOMAIN s 
                             /\ "body" \in DOMAIN s
         [] s.type = Await -> "condition" \in DOMAIN s
         [] s.type = Print -> "expr" \in DOMAIN s
         [] s.type = Assert -> "condition" \in DOMAIN s
         [] s.type = Skip -> TRUE
         [] s.type = Return -> TRUE
         [] s.type = Call -> /\ "procName" \in DOMAIN s 
                             /\ "args" \in DOMAIN s
         [] s.type = Goto -> "label" \in DOMAIN s
         [] s.type = LabeledStmt -> /\ "label" \in DOMAIN s 
                                    /\ "stmts" \in DOMAIN s
         [] OTHER -> FALSE

\* Check if a record is a valid procedure
IsProcedure(p) ==
    /\ p \in [type: {Procedure}]
    /\ "name" \in DOMAIN p
    /\ "params" \in DOMAIN p
    /\ "localVars" \in DOMAIN p
    /\ "body" \in DOMAIN p

\* Check if a record is a valid process
IsProcess(p) ==
    /\ p \in [type: {Process}]
    /\ "name" \in DOMAIN p
    /\ "id" \in DOMAIN p
    /\ "localVars" \in DOMAIN p
    /\ "body" \in DOMAIN p
    /\ "fairness" \in DOMAIN p

\* Check if a record is a valid algorithm
IsAlgorithm(a) ==
    /\ a \in [type: {Algorithm}]
    /\ "name" \in DOMAIN a
    /\ "globalVars" \in DOMAIN a
    /\ "procedures" \in DOMAIN a
    /\ "processes" \in DOMAIN a
    /\ "fairness" \in DOMAIN a

-----------------------------------------------------------------------------
(* Translation Pipeline Phases *)

TranslationPhases == {"Parse", "Explode", "TranslateControl", 
                      "AddSubscripts", "GenerateOutput", "Done", "Error"}

\* Phase 1: Explode structured labeled statements
\* Converts nested labeled statements into flat sequence

RECURSIVE ExplodeStmt(_, _)
ExplodeStmt(stmt, nextLabel) ==
    IF stmt.type = LabeledStmt THEN
        LET innerStmts == stmt.stmts
            currentLabel == stmt.label
        IN [label |-> currentLabel, 
            stmts |-> innerStmts, 
            nextLabel |-> nextLabel]
    ELSE
        [label |-> "anonymous", 
         stmts |-> <<stmt>>, 
         nextLabel |-> nextLabel]

RECURSIVE ExplodeStmtSeq(_, _)
ExplodeStmtSeq(stmts, finalLabel) ==
    IF Len(stmts) = 0 THEN <<>>
    ELSE IF Len(stmts) = 1 THEN <<ExplodeStmt(stmts[1], finalLabel)>>
    ELSE 
        LET first == stmts[1]
            rest == SubSeq(stmts, 2, Len(stmts))
            restExploded == ExplodeStmtSeq(rest, finalLabel)
            nextLbl == IF Len(restExploded) > 0 THEN restExploded[1].label ELSE finalLabel
        IN <<ExplodeStmt(first, nextLbl)>> \o restExploded

\* Phase 2: Translate control flow (calls, returns, gotos)

TranslateCall(callStmt, returnLabel, procDefs) ==
    LET procName == callStmt.procName
        args == callStmt.args
    IN [type |-> "TranslatedCall",
        pushStack |-> TRUE,
        returnPC |-> returnLabel,
        targetProc |-> procName,
        argAssignments |-> args]

TranslateReturn(procName, params) ==
    [type |-> "TranslatedReturn",
     popStack |-> TRUE,
     restorePC |-> TRUE,
     clearParams |-> params]

TranslateGoto(gotoStmt) ==
    [type |-> "TranslatedGoto",
     targetLabel |-> gotoStmt.label]

\* Phase 3: Add subscripts for process-local variables

AddProcessSubscript(varName, processId) ==
    [type |-> "SubscriptedVar",
     baseName |-> varName,
     subscript |-> processId]

RECURSIVE AddSubscriptsToExpr(_, _, _)
AddSubscriptsToExpr(expr, localVarNames, processId) ==
    CASE expr.type = Identifier ->
            IF expr.name \in localVarNames 
            THEN [type |-> Identifier, 
                  name |-> expr.name, 
                  subscript |-> processId]
            ELSE expr
      [] expr.type = BinOp ->
            [type |-> BinOp,
             op |-> expr.op,
             left |-> AddSubscriptsToExpr(expr.left, localVarNames, processId),
             right |-> AddSubscriptsToExpr(expr.right, localVarNames, processId)]
      [] expr.type = UnaryOp ->
            [type |-> UnaryOp,
             op |-> expr.op,
             operand |-> AddSubscriptsToExpr(expr.operand, localVarNames, processId)]
      [] expr.type = FuncApp ->
            [type |-> FuncApp,
             func |-> expr.func,
             args |-> expr.args]
      [] OTHER -> expr

-----------------------------------------------------------------------------
(* TLA+ Output Generation *)

\* Generate Init predicate
GenerateInit(algorithm) ==
    LET gVars == algorithm.globalVars
        procs == algorithm.processes
        initGlobals == [v \in {gv.name : gv \in gVars} |-> 
                        CHOOSE gv \in gVars : gv.name = v]
        initPC == [p \in {pr.name : pr \in procs} |-> 
                   IF Len(pr.body) > 0 
                   THEN IF pr.body[1].type = LabeledStmt 
                        THEN pr.body[1].label 
                        ELSE "Start"
                   ELSE "Done"]
    IN [globals |-> initGlobals,
        pc |-> initPC,
        stack |-> [p \in {pr.name : pr \in procs} |-> <<>>]]

\* Generate Next relation
GenerateNext(algorithm, exploded) ==
    LET procs == algorithm.processes
        procActions == {[processName |-> p.name, 
                        labels |-> {e.label : e \in exploded}] : p \in procs}
    IN [actions |-> procActions,
        stutterCondition |-> TRUE]

\* Generate fairness conditions based on algorithm's fairness setting
GenerateFairness(algorithm, nextAction) ==
    LET fairOpt == algorithm.fairness
        procs == algorithm.processes
    IN CASE fairOpt = NoFairness -> 
              [type |-> "None"]
         [] fairOpt = WeakFairProcess -> 
              [type |-> "WF_vars", 
               actions |-> {p.name : p \in procs}]
         [] fairOpt = WeakFairNext -> 
              [type |-> "WF_vars", 
               action |-> nextAction]
         [] fairOpt = StrongFairProcess -> 
              [type |-> "SF_vars", 
               actions |-> {p.name : p \in procs}]
         [] OTHER -> 
              [type |-> "None"]

\* Generate Spec formula
GenerateSpec(initPred, nextRel, fairCond) ==
    [init |-> initPred,
     next |-> nextRel,
     fairness |-> fairCond,
     formula |-> "Init /\\ [][Next]_vars /\\ Fairness"]

\* Generate Termination property
GenerateTermination(algorithm) ==
    LET procs == algorithm.processes
        allDone == [p \in {pr.name : pr \in procs} |-> "Done"]
    IN [property |-> "Termination",
        formula |-> "<>(\\A self \\in ProcSet: pc[self] = \"Done\")",
        condition |-> allDone]

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ ast = [type |-> Algorithm,
              name |-> "Empty",
              globalVars |-> {},
              procedures |-> {},
              processes |-> {},
              fairness |-> NoFairness]
    /\ translationPhase = "Parse"
    /\ explodedStmts = <<>>
    /\ translatedStmts = <<>>
    /\ subscriptedVars = {}
    /\ tlaPlusInit = [globals |-> {}, pc |-> {}, stack |-> {}]
    /\ tlaPlusNext = [actions |-> {}, stutterCondition |-> TRUE]
    /\ tlaPlusSpec = [init |-> {}, next |-> {}, fairness |-> {}, formula |-> ""]
    /\ tlaPlusTermination = [property |-> "", formula |-> "", condition |-> {}]
    /\ tlaPlusFairness = [type |-> "None"]
    /\ processSet = {}
    /\ procedureSet = {}
    /\ globalVars = {}
    /\ localVars = {}
    /\ pcVar = [v |-> {}]
    /\ stackVar = [v |-> {}]
    /\ translationError = ""

-----------------------------------------------------------------------------
(* State Transitions *)

\* Load a new AST for translation
LoadAST(newAst) ==
    /\ IsAlgorithm(newAst)
    /\ translationPhase = "Parse"
    /\ ast' = newAst
    /\ processSet' = newAst.processes
    /\ procedureSet' = newAst.procedures
    /\ globalVars' = newAst.globalVars
    /\ localVars' = UNION {p.localVars : p \in newAst.processes}
    /\ UNCHANGED <<translationPhase, explodedStmts, translatedStmts,
                   subscriptedVars, tlaPlusInit, tlaPlusNext, tlaPlusSpec,
                   tlaPlusTermination, tlaPlusFairness, pcVar, stackVar,
                   translationError>>

\* Phase transition: Parse -> Explode
DoExplode ==
    /\ translationPhase = "Parse"
    /\ IsAlgorithm(ast)
    /\ LET allBodies == UNION {p.body : p \in ast.processes}
       IN explodedStmts' = allBodies
    /\ translationPhase' = "Explode"
    /\ UNCHANGED <<ast, translatedStmts, subscriptedVars, tlaPlusInit,
                   tlaPlusNext, tlaPlusSpec, tlaPlusTermination, 
                   tlaPlusFairness, processSet, procedureSet, globalVars,
                   localVars, pcVar, stackVar, translationError>>

\* Phase transition: Explode -> TranslateControl
DoTranslateControl ==
    /\ translationPhase = "Explode"
    /\ translatedStmts' = explodedStmts
    /\ translationPhase' = "TranslateControl"
    /\ UNCHANGED <<ast, explodedStmts, subscriptedVars, tlaPlusInit,
                   tlaPlusNext, tlaPlusSpec, tlaPlusTermination,
                   tlaPlusFairness, processSet, procedureSet, globalVars,
                   localVars, pcVar, stackVar, translationError>>

\* Phase transition: TranslateControl -> AddSubscripts
DoAddSubscripts ==
    /\ translationPhase = "TranslateControl"
    /\ LET varNames == {v.name : v \in localVars}
       IN subscriptedVars' = varNames
    /\ translationPhase' = "AddSubscripts"
    /\ UNCHANGED <<ast, explodedStmts, translatedStmts, tlaPlusInit,
                   tlaPlusNext, tlaPlusSpec, tlaPlusTermination,
                   tlaPlusFairness, processSet, procedureSet, globalVars,
                   localVars, pcVar, stackVar, translationError>>

\* Phase transition: AddSubscripts -> GenerateOutput
DoGenerateOutput ==
    /\ translationPhase = "AddSubscripts"
    /\ tlaPlusInit' = GenerateInit(ast)
    /\ tlaPlusNext' = GenerateNext(ast, translatedStmts)
    /\ tlaPlusFairness' = GenerateFairness(ast, tlaPlusNext')
    /\ tlaPlusSpec' = GenerateSpec(tlaPlusInit', tlaPlusNext', tlaPlusFairness')
    /\ tlaPlusTermination' = GenerateTermination(ast)
    /\ pcVar' = [v |-> {p.name : p \in ast.processes}]
    /\ stackVar' = [v |-> {p.name : p \in ast.processes}]
    /\ translationPhase' = "GenerateOutput"
    /\ UNCHANGED <<ast, explodedStmts, translatedStmts, subscriptedVars,
                   processSet, procedureSet, globalVars, localVars,
                   translationError>>

\* Phase transition: GenerateOutput -> Done
FinishTranslation ==
    /\ translationPhase = "GenerateOutput"
    /\ translationPhase' = "Done"
    /\ UNCHANGED <<ast, explodedStmts, translatedStmts, subscriptedVars,
                   tlaPlusInit, tlaPlusNext, tlaPlusSpec, tlaPlusTermination,
                   tlaPlusFairness, processSet, procedureSet, globalVars,
                   localVars, pcVar, stackVar, translationError>>

\* Error handling
ReportError(errorMsg) ==
    /\ translationPhase /= "Done"
    /\ translationPhase /= "Error"
    /\ translationError' = errorMsg
    /\ translationPhase' = "Error"
    /\ UNCHANGED <<ast, explodedStmts, translatedStmts, subscriptedVars,
                   tlaPlusInit, tlaPlusNext, tlaPlusSpec, tlaPlusTermination,
                   tlaPlusFairness, processSet, procedureSet, globalVars,
                   localVars, pcVar, stackVar>>

\* Next state relation
Next ==
    \/ \E newAst \in [type: {Algorithm}, 
                      name: {"Test"}, 
                      globalVars: SUBSET [type: {VarDecl}, name: {"x", "y"}, initValue: {0, 1}],
                      procedures: {{}},
                      processes: SUBSET [type: {Process}, name: {"P"}, id: {1}, 
                                        localVars: {{}}, body: {{}}, fairness: {NoFairness}],
                      fairness: {NoFairness, WeakFairProcess, WeakFairNext, StrongFairProcess}] :
         LoadAST(newAst)
    \/ DoExplode
    \/ DoTranslateControl
    \/ DoAddSubscripts
    \/ DoGenerateOutput
    \/ FinishTranslation
    \/ ReportError("Translation failed")

-----------------------------------------------------------------------------
(* Safety Invariants *)

\* Translation phase is always valid
TypeInvariant ==
    /\ translationPhase \in TranslationPhases
    /\ translationError \in STRING

\* If translation is done, output is well-formed
OutputWellFormed ==
    translationPhase = "Done" =>
        /\ "globals" \in DOMAIN tlaPlusInit
        /\ "pc" \in DOMAIN tlaPlusInit
        /\ "actions" \in DOMAIN tlaPlusNext
        /\ "formula" \in DOMAIN tlaPlusSpec
        /\ "property" \in DOMAIN tlaPlusTermination

\* Error state is terminal
ErrorTerminal ==
    translationPhase = "Error" => translationError /= ""

\* PC variable tracks all processes
PCTracksProcesses ==
    translationPhase = "Done" =>
        pcVar.v = {p.name : p \in ast.processes}

\* Fairness is correctly generated
FairnessCorrect ==
    translationPhase = "Done" =>
        CASE ast.fairness = NoFairness -> tlaPlusFairness.type = "None"
          [] ast.fairness = WeakFairProcess -> tlaPlusFairness.type = "WF_vars"
          [] ast.fairness = WeakFairNext -> tlaPlusFairness.type = "WF_vars"
          [] ast.fairness = StrongFairProcess -> tlaPlusFairness.type = "SF_vars"
          [] OTHER -> TRUE

\* Combined invariant
Inv ==
    /\ TypeInvariant
    /\ OutputWellFormed
    /\ ErrorTerminal
    /\ PCTracksProcesses
    /\ FairnessCorrect

-----------------------------------------------------------------------------
(* Liveness Properties *)

\* Translation eventually completes or errors
TranslationTerminates ==
    <>(translationPhase = "Done" \/ translationPhase = "Error")

\* If we start translating, we make progress
TranslationProgress ==
    [](translationPhase = "Parse" => <>(translationPhase /= "Parse"))

\* Well-formed input leads to successful translation
WellFormedInputSucceeds ==
    []((/\ translationPhase = "Parse" 
        /\ IsAlgorithm(ast)) => <>(translationPhase = "Done"))

-----------------------------------------------------------------------------
(* Fairness Conditions *)

\* Weak fairness on all translation steps
FairnessCondition ==
    /\ WF_vars(DoExplode)
    /\ WF_vars(DoTranslateControl)
    /\ WF_vars(DoAddSubscripts)
    /\ WF_vars(DoGenerateOutput)
    /\ WF_vars(FinishTranslation)

-----------------------------------------------------------------------------
(* Specification *)

Spec == 
    /\ Init 
    /\ [][Next]_vars 
    /\ FairnessCondition

-----------------------------------------------------------------------------
(* Theorems for TLC *)

THEOREM Spec => []Inv

THEOREM Spec => TranslationTerminates

=============================================================================