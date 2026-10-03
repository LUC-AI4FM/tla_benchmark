---------------------------- MODULE PlusCal2TLA ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    \* AST Node Types
    NodeTypes,
    \* Variable identifiers
    VarIds,
    \* Process identifiers  
    ProcIds,
    \* Label identifiers
    LabelIds,
    \* Expression identifiers (for TLA+ expressions embedded in PlusCal)
    ExprIds,
    \* Fairness options: "none", "wf_procs", "wf_next", "sf_procs"
    FairnessOption

VARIABLES
    \* The input abstract syntax tree
    ast,
    \* The current translation phase
    phase,
    \* Intermediate representation during translation
    ir,
    \* The output TLA+ specification components
    initPred,
    nextAction,
    specFormula,
    terminationProp,
    \* Process-local variable mappings
    varSubscripts,
    \* Label to statement mappings after explosion
    labeledStmts,
    \* Error state (empty string means no error)
    errorState

vars == <<ast, phase, ir, initPred, nextAction, specFormula, 
          terminationProp, varSubscripts, labeledStmts, errorState>>

-----------------------------------------------------------------------------
(* AST Grammar Definitions *)

\* An identifier is a string from the appropriate set
IsVarId(v) == v \in VarIds
IsProcId(p) == p \in ProcIds
IsLabelId(l) == l \in LabelIds
IsExprId(e) == e \in ExprIds

\* Basic AST node structure
IsASTNode(n) == 
    /\ n \in [type: NodeTypes, children: Seq(NodeTypes), attrs: [STRING -> STRING]]

\* Variable declaration node
IsVarDecl(n) ==
    /\ n.type = "VarDecl"
    /\ "name" \in DOMAIN n.attrs
    /\ "initValue" \in DOMAIN n.attrs
    /\ IsVarId(n.attrs.name)

\* Assignment statement node
IsAssignment(n) ==
    /\ n.type = "Assignment"
    /\ "lhs" \in DOMAIN n.attrs
    /\ "rhs" \in DOMAIN n.attrs

\* If statement node
IsIfStmt(n) ==
    /\ n.type = "If"
    /\ "condition" \in DOMAIN n.attrs
    /\ Len(n.children) >= 1  \* At least then branch

\* While statement node
IsWhileStmt(n) ==
    /\ n.type = "While"
    /\ "condition" \in DOMAIN n.attrs
    /\ Len(n.children) >= 1  \* Loop body

\* Call statement node
IsCallStmt(n) ==
    /\ n.type = "Call"
    /\ "procedure" \in DOMAIN n.attrs
    /\ "args" \in DOMAIN n.attrs

\* Return statement node
IsReturnStmt(n) ==
    /\ n.type = "Return"

\* Goto statement node
IsGotoStmt(n) ==
    /\ n.type = "Goto"
    /\ "target" \in DOMAIN n.attrs
    /\ IsLabelId(n.attrs.target)

\* Labeled statement node
IsLabeledStmt(n) ==
    /\ n.type = "LabeledStmt"
    /\ "label" \in DOMAIN n.attrs
    /\ IsLabelId(n.attrs.label)
    /\ Len(n.children) >= 1

\* Process definition node
IsProcessDef(n) ==
    /\ n.type = "Process"
    /\ "id" \in DOMAIN n.attrs
    /\ "idSet" \in DOMAIN n.attrs  \* Set of process instance ids
    /\ IsProcId(n.attrs.id)

\* Procedure definition node
IsProcedureDef(n) ==
    /\ n.type = "Procedure"
    /\ "name" \in DOMAIN n.attrs
    /\ "params" \in DOMAIN n.attrs

\* Algorithm node (root of AST)
IsAlgorithm(n) ==
    /\ n.type = "Algorithm"
    /\ "name" \in DOMAIN n.attrs
    /\ "globalVars" \in DOMAIN n.attrs
    /\ "processes" \in DOMAIN n.attrs

\* Statement types union
IsStatement(n) ==
    \/ IsAssignment(n)
    \/ IsIfStmt(n)
    \/ IsWhileStmt(n)
    \/ IsCallStmt(n)
    \/ IsReturnStmt(n)
    \/ IsGotoStmt(n)
    \/ IsLabeledStmt(n)

-----------------------------------------------------------------------------
(* Translation Phases *)

Phases == {"Init", "Explode", "TranslateControl", "AddSubscripts", 
           "ConstructSpec", "Done", "Error"}

\* Valid phase transitions
ValidTransition(from, to) ==
    \/ from = "Init" /\ to = "Explode"
    \/ from = "Explode" /\ to = "TranslateControl"
    \/ from = "TranslateControl" /\ to = "AddSubscripts"
    \/ from = "AddSubscripts" /\ to = "ConstructSpec"
    \/ from = "ConstructSpec" /\ to = "Done"
    \/ to = "Error"  \* Can always transition to error

-----------------------------------------------------------------------------
(* Helper Functions for Translation *)

\* Extract all labels from AST
RECURSIVE ExtractLabels(_)
ExtractLabels(node) ==
    IF node.type = "LabeledStmt" 
    THEN {node.attrs.label} \union 
         UNION {ExtractLabels(node.children[i]) : i \in 1..Len(node.children)}
    ELSE IF Len(node.children) > 0
         THEN UNION {ExtractLabels(node.children[i]) : i \in 1..Len(node.children)}
         ELSE {}

\* Extract all variables from AST
RECURSIVE ExtractVars(_)
ExtractVars(node) ==
    IF node.type = "VarDecl"
    THEN {node.attrs.name}
    ELSE IF Len(node.children) > 0
         THEN UNION {ExtractVars(node.children[i]) : i \in 1..Len(node.children)}
         ELSE {}

\* Extract all processes from AST
RECURSIVE ExtractProcesses(_)
ExtractProcesses(node) ==
    IF node.type = "Process"
    THEN {node.attrs.id}
    ELSE IF Len(node.children) > 0
         THEN UNION {ExtractProcesses(node.children[i]) : i \in 1..Len(node.children)}
         ELSE {}

\* Check if variable is process-local
IsLocalVar(varName, procId, astNode) ==
    \* Simplified check - in real implementation would traverse AST
    /\ varName \in VarIds
    /\ procId \in ProcIds

\* Generate subscripted variable name
SubscriptVar(varName, procId) ==
    \* Concatenate variable name with process id subscript
    [var |-> varName, proc |-> procId]

-----------------------------------------------------------------------------
(* Phase 1: Explode Structured Labeled Statements *)

\* Explode breaks apart complex labeled statements into atomic steps
\* Each label becomes a separate action in the TLA+ spec

ExplodeLabeledStmt(lstmt) ==
    \* Returns sequence of simple labeled statements
    IF lstmt.type = "LabeledStmt"
    THEN [label |-> lstmt.attrs.label, 
          body |-> lstmt.children,
          nextLabel |-> IF "fallthrough" \in DOMAIN lstmt.attrs 
                        THEN lstmt.attrs.fallthrough 
                        ELSE "Done"]
    ELSE [label |-> "error", body |-> <<>>, nextLabel |-> "Error"]

RECURSIVE ExplodeAll(_)
ExplodeAll(stmts) ==
    IF stmts = <<>>
    THEN <<>>
    ELSE <<ExplodeLabeledStmt(Head(stmts))>> \o ExplodeAll(Tail(stmts))

DoExplode ==
    /\ phase = "Explode"
    /\ ast.type = "Algorithm"
    /\ LET exploded == [p \in ExtractProcesses(ast) |-> 
                        ExplodeAll(ast.children)]
       IN labeledStmts' = exploded
    /\ phase' = "TranslateControl"
    /\ UNCHANGED <<ast, ir, initPred, nextAction, specFormula, 
                   terminationProp, varSubscripts, errorState>>

-----------------------------------------------------------------------------
(* Phase 2: Translate Calls, Returns, Gotos *)

\* Translate a call into stack push + goto
TranslateCall(callStmt, returnLabel) ==
    [type |-> "Sequence",
     children |-> <<
        [type |-> "StackPush", 
         attrs |-> [returnAddr |-> returnLabel, 
                    args |-> callStmt.attrs.args]],
        [type |-> "Goto",
         attrs |-> [target |-> callStmt.attrs.procedure]]
     >>]

\* Translate a return into stack pop + goto
TranslateReturn(retStmt) ==
    [type |-> "Sequence",
     children |-> <<
        [type |-> "StackPop", attrs |-> [result |-> ""]],
        [type |-> "GotoReturn", attrs |-> []]
     >>]

\* Translate goto (mostly unchanged, just validate target)
TranslateGoto(gotoStmt, validLabels) ==
    IF gotoStmt.attrs.target \in validLabels
    THEN gotoStmt
    ELSE [type |-> "Error", 
          attrs |-> [msg |-> "Invalid goto target"]]

RECURSIVE TranslateControlStmt(_,_)
TranslateControlStmt(stmt, ctx) ==
    CASE stmt.type = "Call" -> TranslateCall(stmt, ctx.returnLabel)
      [] stmt.type = "Return" -> TranslateReturn(stmt)
      [] stmt.type = "Goto" -> TranslateGoto(stmt, ctx.validLabels)
      [] OTHER -> stmt

DoTranslateControl ==
    /\ phase = "TranslateControl"
    /\ LET validLabels == UNION {DOMAIN labeledStmts[p] : p \in DOMAIN labeledStmts}
           ctx == [returnLabel |-> "Done", validLabels |-> validLabels]
       IN ir' = [p \in DOMAIN labeledStmts |->
                 [l \in DOMAIN labeledStmts[p] |->
                  [labeledStmts[p][l] EXCEPT 
                   !.body = TranslateControlStmt(labeledStmts[p][l].body, ctx)]]]
    /\ phase' = "AddSubscripts"
    /\ UNCHANGED <<ast, initPred, nextAction, specFormula, 
                   terminationProp, varSubscripts, labeledStmts, errorState>>

-----------------------------------------------------------------------------
(* Phase 3: Add Subscripts for Process-Local Variables *)

\* For each process-local variable, add [self] subscript
RECURSIVE AddSubscriptsToExpr(_,_)
AddSubscriptsToExpr(expr, localVars) ==
    IF expr.type = "VarRef" /\ expr.attrs.name \in localVars
    THEN [expr EXCEPT !.attrs.subscript = "self"]
    ELSE IF Len(expr.children) > 0
         THEN [expr EXCEPT !.children = 
               [i \in 1..Len(expr.children) |-> 
                AddSubscriptsToExpr(expr.children[i], localVars)]]
         ELSE expr

DoAddSubscripts ==
    /\ phase = "AddSubscripts"
    /\ LET localVars == ExtractVars(ast) \ ast.attrs.globalVars
       IN varSubscripts' = [v \in localVars |-> "self"]
    /\ phase' = "ConstructSpec"
    /\ UNCHANGED <<ast, ir, initPred, nextAction, specFormula, 
                   terminationProp, labeledStmts, errorState>>

-----------------------------------------------------------------------------
(* Phase 4: Construct Init, Next, Spec, Termination *)

\* Build Init predicate from variable declarations
ConstructInit(algAst) ==
    [type |-> "Conjunction",
     conjuncts |-> 
       \* Global variables initialization
       {[type |-> "Equality",
         lhs |-> [type |-> "VarRef", attrs |-> [name |-> v]],
         rhs |-> algAst.attrs.globalVars[v].initValue]
        : v \in DOMAIN algAst.attrs.globalVars}
       \union
       \* PC initialization for each process
       {[type |-> "Equality",
         lhs |-> [type |-> "VarRef", attrs |-> [name |-> "pc", subscript |-> p]],
         rhs |-> [type |-> "StringLit", value |-> "Start"]]
        : p \in ExtractProcesses(algAst)}]

\* Build action for a labeled statement
ConstructAction(procId, label, lstmt) ==
    [type |-> "Action",
     name |-> procId \o "_" \o label,
     guard |-> [type |-> "Equality",
                lhs |-> [type |-> "VarRef", 
                        attrs |-> [name |-> "pc", subscript |-> procId]],
                rhs |-> [type |-> "StringLit", value |-> label]],
     body |-> lstmt.body,
     pcUpdate |-> [type |-> "Equality",
                   lhs |-> [type |-> "Prime",
                           child |-> [type |-> "VarRef",
                                     attrs |-> [name |-> "pc", 
                                               subscript |-> procId]]],
                   rhs |-> [type |-> "StringLit", value |-> lstmt.nextLabel]]]

\* Build Next action as disjunction of all process actions
ConstructNext(irMap) ==
    [type |-> "Disjunction",
     disjuncts |-> 
       UNION {{ConstructAction(p, l, irMap[p][l]) 
               : l \in DOMAIN irMap[p]} 
              : p \in DOMAIN irMap}]

\* Build Spec formula based on fairness option
ConstructSpec(initP, nextA, fairness, processes) ==
    LET baseSpec == [type |-> "Temporal",
                     op |-> "[]",
                     child |-> [type |-> "Leads",
                               from |-> initP,
                               to |-> nextA]]
        wfProcs == [type |-> "Conjunction",
                    conjuncts |-> {[type |-> "WeakFairness",
                                   action |-> p \o "_action",
                                   vars |-> "vars"]
                                  : p \in processes}]
        sfProcs == [type |-> "Conjunction",
                    conjuncts |-> {[type |-> "StrongFairness",
                                   action |-> p \o "_action",
                                   vars |-> "vars"]
                                  : p \in processes}]
        wfNext == [type |-> "WeakFairness",
                   action |-> "Next",
                   vars |-> "vars"]
    IN CASE fairness = "none" -> baseSpec
         [] fairness = "wf_procs" -> 
            [type |-> "Conjunction", 
             conjuncts |-> {baseSpec, wfProcs}]
         [] fairness = "wf_next" ->
            [type |-> "Conjunction",
             conjuncts |-> {baseSpec, wfNext}]
         [] fairness = "sf_procs" ->
            [type |-> "Conjunction",
             conjuncts |-> {baseSpec, sfProcs}]
         [] OTHER -> baseSpec

\* Build Termination property
ConstructTermination(processes) ==
    [type |-> "Temporal",
     op |-> "<>",
     child |-> [type |-> "Conjunction",
                conjuncts |-> {[type |-> "Equality",
                               lhs |-> [type |-> "VarRef",
                                       attrs |-> [name |-> "pc", 
                                                 subscript |-> p]],
                               rhs |-> [type |-> "StringLit", 
                                       value |-> "Done"]]
                              : p \in processes}]]

DoConstructSpec ==
    /\ phase = "ConstructSpec"
    /\ LET procs == ExtractProcesses(ast)
           init == ConstructInit(ast)
           next == ConstructNext(ir)
       IN /\ initPred' = init
          /\ nextAction' = next
          /\ specFormula' = ConstructSpec(init, next, FairnessOption, procs)
          /\ terminationProp' = ConstructTermination(procs)
    /\ phase' = "Done"
    /\ UNCHANGED <<ast, ir, varSubscripts, labeledStmts, errorState>>

-----------------------------------------------------------------------------
(* Error Handling *)

ReportError(msg) ==
    /\ errorState' = msg
    /\ phase' = "Error"
    /\ UNCHANGED <<ast, ir, initPred, nextAction, specFormula,
                   terminationProp, varSubscripts, labeledStmts>>

\* Check for common errors
CheckErrors ==
    /\ phase # "Error"
    /\ phase # "Done"
    /\ \/ ast.type # "Algorithm" /\ ReportError("Root must be Algorithm node")
       \/ ExtractLabels(ast) = {} /\ ReportError("No labels found in algorithm")
       \/ ExtractProcesses(ast) = {} /\ 
          ReportError("No processes found in algorithm")

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ ast \in [type: {"Algorithm"}, 
                children: Seq([type: NodeTypes, children: Seq(NodeTypes), 
                              attrs: [STRING -> STRING]]),
                attrs: [name: STRING, globalVars: [VarIds -> [initValue: STRING]],
                       processes: SUBSET ProcIds]]
    /\ phase = "Init"
    /\ ir = [x \in {} |-> {}]
    /\ initPred = [type |-> "Empty"]
    /\ nextAction = [type |-> "Empty"]
    /\ specFormula = [type |-> "Empty"]
    /\ terminationProp = [type |-> "Empty"]
    /\ varSubscripts = [x \in {} |-> ""]
    /\ labeledStmts = [x \in {} |-> {}]
    /\ errorState = ""

-----------------------------------------------------------------------------
(* Next State Relation *)

StartTranslation ==
    /\ phase = "Init"
    /\ ast.type = "Algorithm"
    /\ phase' = "Explode"
    /\ UNCHANGED <<ast, ir, initPred, nextAction, specFormula,
                   terminationProp, varSubscripts, labeledStmts, errorState>>

Next ==
    \/ StartTranslation
    \/ DoExplode
    \/ DoTranslateControl
    \/ DoAddSubscripts
    \/ DoConstructSpec
    \/ CheckErrors
    \/ /\ phase \in {"Done", "Error"}
       /\ UNCHANGED vars

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety Invariants *)

\* Phase is always valid
TypeInvariant ==
    /\ phase \in Phases
    /\ errorState \in STRING

\* Phase transitions are valid
PhaseTransitionInvariant ==
    [][ValidTransition(phase, phase')]_phase

\* If no error, certain properties hold
ConsistencyInvariant ==
    errorState = "" =>
        /\ phase \in Phases
        /\ ast.type = "Algorithm" => ExtractProcesses(ast) # {}

\* Output is well-formed when done
OutputInvariant ==
    phase = "Done" =>
        /\ initPred.type # "Empty"
        /\ nextAction.type # "Empty"
        /\ specFormula.type # "Empty"
        /\ terminationProp.type # "Empty"

-----------------------------------------------------------------------------
(* Liveness Properties *)

\* Translation eventually completes or errors
TranslationTerminates ==
    <>(phase \in {"Done", "Error"})

\* If input is valid, translation succeeds
SuccessfulTranslation ==
    (ast.type = "Algorithm" /\ ExtractProcesses(ast) # {} /\ 
     ExtractLabels(ast) # {}) 
    ~> (phase = "Done")

\* Error states are reachable for invalid input
ErrorReachable ==
    (ast.type # "Algorithm") ~> (phase = "Error")

-----------------------------------------------------------------------------
(* Fairness *)

\* The specification includes weak fairness of Next
\* This ensures translation makes progress

Fairness == WF_vars(Next)

=============================================================================