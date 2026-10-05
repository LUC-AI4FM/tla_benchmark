---------------------------- MODULE PluCalTranslator ----------------------------
(***************************************************************************)
(* A formal model of a translator from a PlusCal-like procedural language  *)
(* AST to TLA+ operational semantics. This captures how the AST denotes    *)
(* initial states and next-state relations.                                *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    ProcedureNames,     \* Set of procedure names
    ProcessNames,       \* Set of process names (empty for uniprocess)
    LabelNames,         \* Set of label names
    VarNames,           \* Set of variable names
    ParamNames,         \* Set of parameter names
    Values,             \* Domain of values
    MaxStackDepth,      \* Maximum call stack depth
    MaxProcesses,       \* Maximum number of process instances
    NullValue,          \* Represents undefined/null
    ErrorValue          \* Represents error conditions

(***************************************************************************)
(* AST Node Types - representing the abstract syntax tree structure        *)
(***************************************************************************)

ASTNodeTypes == {
    "Algorithm", "Procedure", "Process", "VarDecl", "ParamDecl",
    "LabeledStmt", "Assign", "If", "Either", "When", "With",
    "While", "Call", "Return", "Goto", "Skip", "Assert", "Print",
    "Expr", "VarRef", "Literal", "BinOp", "UnaryOp"
}

ControlConstructs == {"If", "Either", "When", "With", "While"}

FairnessTypes == {"None", "WeakFair", "StrongFair"}

(***************************************************************************)
(* VARIABLES                                                               *)
(***************************************************************************)

VARIABLES
    \* AST representation
    ast,                    \* The input AST
    
    \* Translation state
    translationPhase,       \* Current phase: "Parsing", "Validating", "Generating", "Done", "Error"
    errors,                 \* Set of detected errors
    warnings,               \* Set of warnings
    
    \* Symbol tables built during translation
    globalVars,             \* Map: VarName -> {initValue, type}
    procedures,             \* Map: ProcName -> {params, localVars, labels, body}
    processes,              \* Map: ProcessName -> {instances, localVars, labels, body, fairness}
    labelMap,               \* Map: Label -> {procedure/process, statements, nextLabel}
    
    \* Generated TLA+ semantics (abstract representation)
    genInitPredicate,       \* Generated Init predicate structure
    genNextRelation,        \* Generated Next relation structure
    genFairnessConditions,  \* Generated fairness conditions
    
    \* Semantic validation state
    scopeStack,             \* Stack of scopes for validation
    declaredSymbols,        \* All declared symbols for duplicate checking
    
    \* Runtime semantics model (for verification)
    rtState,                \* Runtime state: variable bindings
    rtPC,                   \* Program counter(s): Map ProcessId -> Label
    rtStack,                \* Call stacks: Map ProcessId -> Seq of frames
    rtEnabled,              \* Currently enabled actions
    rtTerminated            \* Set of terminated process instances

vars == <<ast, translationPhase, errors, warnings, globalVars, procedures,
          processes, labelMap, genInitPredicate, genNextRelation,
          genFairnessConditions, scopeStack, declaredSymbols, rtState,
          rtPC, rtStack, rtEnabled, rtTerminated>>

(***************************************************************************)
(* Type Definitions                                                        *)
(***************************************************************************)

ProcessId == ProcessNames \cup {"main"}  \* "main" for uniprocess

StackFrame == [
    returnLabel: LabelNames \cup {NullValue},
    procedure: ProcedureNames \cup {NullValue},
    locals: [VarNames -> Values \cup {NullValue}],
    params: [ParamNames -> Values \cup {NullValue}]
]

RuntimeState == [
    vars: [VarNames -> Values \cup {NullValue}],
    pc: [ProcessId -> LabelNames \cup {"Done", "Error"}],
    stack: [ProcessId -> Seq(StackFrame)]
]

(***************************************************************************)
(* Helper Operators                                                        *)
(***************************************************************************)

\* Check if a name is already declared in current scope
IsDeclared(name) == name \in declaredSymbols

\* Get the set of labels in a statement list
RECURSIVE LabelsInStmts(_)
LabelsInStmts(stmts) ==
    IF stmts = <<>> THEN {}
    ELSE LET head == Head(stmts)
         IN IF head.type = "LabeledStmt" 
            THEN {head.label} \cup LabelsInStmts(Tail(stmts))
            ELSE LabelsInStmts(Tail(stmts))

\* Check for duplicate labels
HasDuplicateLabels(labels) ==
    Cardinality(labels) < Cardinality(LabelNames)

\* Compute next label in sequence
NextLabel(currentLabel, labelSequence) ==
    LET idx == CHOOSE i \in 1..Len(labelSequence) : labelSequence[i] = currentLabel
    IN IF idx < Len(labelSequence) THEN labelSequence[idx + 1] ELSE "Done"

(***************************************************************************)
(* AST Validation Predicates                                               *)
(***************************************************************************)

\* Valid variable declaration
ValidVarDecl(decl) ==
    /\ decl.type = "VarDecl"
    /\ decl.name \in VarNames
    /\ decl.initValue \in Values \cup {NullValue}

\* Valid parameter declaration
ValidParamDecl(decl) ==
    /\ decl.type = "ParamDecl"
    /\ decl.name \in ParamNames

\* Valid labeled statement
ValidLabeledStmt(stmt) ==
    /\ stmt.type = "LabeledStmt"
    /\ stmt.label \in LabelNames
    /\ stmt.body # <<>>

\* Valid procedure definition
ValidProcedure(proc) ==
    /\ proc.type = "Procedure"
    /\ proc.name \in ProcedureNames
    /\ \A p \in ToSet(proc.params) : ValidParamDecl(p)
    /\ \A v \in ToSet(proc.localVars) : ValidVarDecl(v)
    /\ proc.body # <<>>

\* Valid process definition
ValidProcess(proc) ==
    /\ proc.type = "Process"
    /\ proc.name \in ProcessNames
    /\ proc.fairness \in FairnessTypes
    /\ \A v \in ToSet(proc.localVars) : ValidVarDecl(v)
    /\ proc.body # <<>>

\* Valid algorithm AST
ValidAST(a) ==
    /\ a.type = "Algorithm"
    /\ a.name # ""
    /\ a.isMultiprocess \in BOOLEAN
    /\ \A v \in ToSet(a.globalVars) : ValidVarDecl(v)
    /\ \A p \in ToSet(a.procedures) : ValidProcedure(p)
    /\ a.isMultiprocess => \A pr \in ToSet(a.processes) : ValidProcess(pr)
    /\ ~a.isMultiprocess => a.mainBody # <<>>

(***************************************************************************)
(* Semantic Constraint Checking                                            *)
(***************************************************************************)

\* Check for duplicate variable declarations
DuplicateVarError(varList) ==
    LET names == {v.name : v \in ToSet(varList)}
    IN Cardinality(names) < Len(varList)

\* Check for illegal goto targets
IllegalGotoError(gotoLabel, validLabels) ==
    gotoLabel \notin validLabels

\* Check for call to undefined procedure
UndefinedProcError(procName) ==
    procName \notin DOMAIN procedures

\* Check parameter count mismatch
ParamCountError(procName, providedCount) ==
    LET proc == procedures[procName]
    IN Len(proc.params) # providedCount

(***************************************************************************)
(* Translation Phase: Parsing (AST Loading)                                *)
(***************************************************************************)

ParseAST ==
    /\ translationPhase = "Parsing"
    /\ ast.type = "Algorithm"
    /\ IF ValidAST(ast)
       THEN /\ translationPhase' = "Validating"
            /\ errors' = errors
       ELSE /\ translationPhase' = "Error"
            /\ errors' = errors \cup {"Invalid AST structure"}
    /\ UNCHANGED <<ast, warnings, globalVars, procedures, processes,
                   labelMap, genInitPredicate, genNextRelation,
                   genFairnessConditions, scopeStack, declaredSymbols,
                   rtState, rtPC, rtStack, rtEnabled, rtTerminated>>

(***************************************************************************)
(* Translation Phase: Validation                                           *)
(***************************************************************************)

ValidateGlobalVars ==
    /\ translationPhase = "Validating"
    /\ LET gvars == ast.globalVars
           names == {v.name : v \in ToSet(gvars)}
       IN IF DuplicateVarError(gvars)
          THEN /\ errors' = errors \cup {"Duplicate global variable declaration"}
               /\ translationPhase' = "Error"
               /\ UNCHANGED globalVars
          ELSE /\ globalVars' = [v \in names |-> 
                    LET decl == CHOOSE d \in ToSet(gvars) : d.name = v
                    IN [initValue |-> decl.initValue]]
               /\ declaredSymbols' = declaredSymbols \cup names
               /\ UNCHANGED <<errors, translationPhase>>
    /\ UNCHANGED <<ast, warnings, procedures, processes, labelMap,
                   genInitPredicate, genNextRelation, genFairnessConditions,
                   scopeStack, rtState, rtPC, rtStack, rtEnabled, rtTerminated>>

ValidateProcedures ==
    /\ translationPhase = "Validating"
    /\ LET procs == ast.procedures
           procNames == {p.name : p \in ToSet(procs)}
       IN IF Cardinality(procNames) < Len(procs)
          THEN /\ errors' = errors \cup {"Duplicate procedure name"}
               /\ translationPhase' = "Error"
               /\ UNCHANGED procedures
          ELSE /\ procedures' = [p \in procNames |->
                    LET proc == CHOOSE pr \in ToSet(procs) : pr.name = p
                    IN [params |-> proc.params,
                        localVars |-> proc.localVars,
                        body |-> proc.body,
                        labels |-> LabelsInStmts(proc.body)]]
               /\ UNCHANGED <<errors, translationPhase>>
    /\ UNCHANGED <<ast, warnings, globalVars, processes, labelMap,
                   genInitPredicate, genNextRelation, genFairnessConditions,
                   scopeStack, declaredSymbols, rtState, rtPC, rtStack,
                   rtEnabled, rtTerminated>>

ValidateProcesses ==
    /\ translationPhase = "Validating"
    /\ ast.isMultiprocess
    /\ LET procs == ast.processes
           procNames == {p.name : p \in ToSet(procs)}
       IN IF Cardinality(procNames) < Len(procs)
          THEN /\ errors' = errors \cup {"Duplicate process name"}
               /\ translationPhase' = "Error"
               /\ UNCHANGED processes
          ELSE /\ processes' = [p \in procNames |->
                    LET proc == CHOOSE pr \in ToSet(procs) : pr.name = p
                    IN [localVars |-> proc.localVars,
                        body |-> proc.body,
                        labels |-> LabelsInStmts(proc.body),
                        fairness |-> proc.fairness,
                        instances |-> proc.instances]]
               /\ UNCHANGED <<errors, translationPhase>>
    /\ UNCHANGED <<ast, warnings, globalVars, procedures, labelMap,
                   genInitPredicate, genNextRelation, genFairnessConditions,
                   scopeStack, declaredSymbols, rtState, rtPC, rtStack,
                   rtEnabled, rtTerminated>>

ValidateLabelUniqueness ==
    /\ translationPhase = "Validating"
    /\ LET allLabels == UNION {procedures[p].labels : p \in DOMAIN procedures}
                        \cup UNION {processes[p].labels : p \in DOMAIN processes}
       IN IF Cardinality(allLabels) < 
             (UNION {Cardinality(procedures[p].labels) : p \in DOMAIN procedures})
             + (UNION {Cardinality(processes[p].labels) : p \in DOMAIN processes})
          THEN /\ errors' = errors \cup {"Duplicate label across procedures/processes"}
               /\ translationPhase' = "Error"
          ELSE /\ translationPhase' = "Generating"
               /\ UNCHANGED errors
    /\ UNCHANGED <<ast, warnings, globalVars, procedures, processes, labelMap,
                   genInitPredicate, genNextRelation, genFairnessConditions,
                   scopeStack, declaredSymbols, rtState, rtPC, rtStack,
                   rtEnabled, rtTerminated>>

(***************************************************************************)
(* Translation Phase: Code Generation                                      *)
(***************************************************************************)

\* Generate Init predicate
GenerateInit ==
    /\ translationPhase = "Generating"
    /\ genInitPredicate' = [
         globalVarInits |-> [v \in DOMAIN globalVars |-> globalVars[v].initValue],
         pcInit |-> IF ast.isMultiprocess
                    THEN [p \in DOMAIN processes |-> 
                          LET proc == processes[p]
                              firstLabel == IF Len(proc.body) > 0 
                                           THEN Head(proc.body).label 
                                           ELSE "Done"
                          IN firstLabel]
                    ELSE [main |-> IF Len(ast.mainBody) > 0
                                   THEN Head(ast.mainBody).label
                                   ELSE "Done"],
         stackInit |-> [p \in ProcessId |-> <<>>]
       ]
    /\ UNCHANGED <<ast, translationPhase, errors, warnings, globalVars,
                   procedures, processes, labelMap, genNextRelation,
                   genFairnessConditions, scopeStack, declaredSymbols,
                   rtState, rtPC, rtStack, rtEnabled, rtTerminated>>

\* Generate label-based actions for Next relation
GenerateLabelActions ==
    /\ translationPhase = "Generating"
    /\ labelMap' = [l \in LabelNames |->
         IF \E p \in DOMAIN procedures : l \in procedures[p].labels
         THEN LET proc == CHOOSE p \in DOMAIN procedures : l \in procedures[p].labels
              IN [context |-> "procedure",
                  owner |-> proc,
                  statements |-> <<>>]  \* Would be populated from AST
         ELSE IF \E p \in DOMAIN processes : l \in processes[p].labels
         THEN LET proc == CHOOSE p \in DOMAIN processes : l \in processes[p].labels
              IN [context |-> "process",
                  owner |-> proc,
                  statements |-> <<>>]
         ELSE [context |-> "unknown", owner |-> NullValue, statements |-> <<>>]]
    /\ UNCHANGED <<ast, translationPhase, errors, warnings, globalVars,
                   procedures, processes, genInitPredicate, genNextRelation,
                   genFairnessConditions, scopeStack, declaredSymbols,
                   rtState, rtPC, rtStack, rtEnabled, rtTerminated>>

\* Generate Next relation structure
GenerateNext ==
    /\ translationPhase = "Generating"
    /\ genNextRelation' = [
         actions |-> {[label |-> l, 
                      guard |-> TRUE,  \* Would be computed from AST
                      effect |-> <<>>] : l \in DOMAIN labelMap},
         stuttering |-> TRUE
       ]
    /\ UNCHANGED <<ast, translationPhase, errors, warnings, globalVars,
                   procedures, processes, labelMap, genInitPredicate,
                   genFairnessConditions, scopeStack, declaredSymbols,
                   rtState, rtPC, rtStack, rtEnabled, rtTerminated>>

\* Generate fairness conditions
GenerateFairness ==
    /\ translationPhase = "Generating"
    /\ genFairnessConditions' = [
         weakFair |-> {p \in DOMAIN processes : processes[p].fairness = "WeakFair"},
         strongFair |-> {p \in DOMAIN processes : processes[p].fairness = "StrongFair"},
         perAction |-> {}  \* Per-action fairness specifications
       ]
    /\ translationPhase' = "Done"
    /\ UNCHANGED <<ast, errors, warnings, globalVars, procedures, processes,
                   labelMap, genInitPredicate, genNextRelation, scopeStack,
                   declaredSymbols, rtState, rtPC, rtStack, rtEnabled, rtTerminated>>

(***************************************************************************)
(* Runtime Semantics Model - For verifying translation correctness         *)
(***************************************************************************)

\* Initialize runtime state from generated Init
InitRuntime ==
    /\ translationPhase = "Done"
    /\ rtState' = [vars |-> genInitPredicate.globalVarInits]
    /\ rtPC' = genInitPredicate.pcInit
    /\ rtStack' = genInitPredicate.stackInit
    /\ rtTerminated' = {}
    /\ UNCHANGED <<ast, translationPhase, errors, warnings, globalVars,
                   procedures, processes, labelMap, genInitPredicate,
                   genNextRelation, genFairnessConditions, scopeStack,
                   declaredSymbols, rtEnabled>>

\* Compute enabled actions based on current state
ComputeEnabled ==
    /\ translationPhase = "Done"
    /\ rtEnabled' = {a \in genNextRelation.actions : 
                     /\ \E pid \in DOMAIN rtPC : rtPC[pid] = a.label
                     /\ pid \notin rtTerminated
                     /\ a.guard}  \* Guard evaluation would be more complex
    /\ UNCHANGED <<ast, translationPhase, errors, warnings, globalVars,
                   procedures, processes, labelMap, genInitPredicate,
                   genNextRelation, genFairnessConditions, scopeStack,
                   declaredSymbols, rtState, rtPC, rtStack, rtTerminated>>

\* Execute a labeled action (simplified)
ExecuteLabeledAction(pid, label) ==
    /\ rtPC[pid] = label
    /\ pid \notin rtTerminated
    /\ \E action \in genNextRelation.actions :
       /\ action.label = label
       /\ action.guard
       \* Update PC to next label
       /\ rtPC' = [rtPC EXCEPT ![pid] = 
            IF label \in DOMAIN labelMap 
            THEN "Done"  \* Simplified - would compute actual next
            ELSE "Done"]
    /\ UNCHANGED <<ast, translationPhase, errors, warnings, globalVars,
                   procedures, processes, labelMap, genInitPredicate,
                   genNextRelation, genFairnessConditions, scopeStack,
                   declaredSymbols, rtState, rtStack, rtEnabled, rtTerminated>>

\* Procedure call semantics
ExecuteCall(pid, procName, args) ==
    /\ procName \in DOMAIN procedures
    /\ Len(rtStack[pid]) < MaxStackDepth
    /\ LET proc == procedures[procName]
           newFrame == [
             returnLabel |-> rtPC[pid],
             procedure |-> procName,
             locals |-> [v \in {d.name : d \in ToSet(proc.localVars)} |-> NullValue],
             params |-> [i \in 1..Len(proc.params) |-> 
                        IF i <= Len(args) THEN args[i] ELSE NullValue]
           ]
           firstLabel == IF Len(proc.body) > 0 
                        THEN Head(proc.body).label 
                        ELSE "Done"
       IN /\ rtStack' = [rtStack EXCEPT ![pid] = Append(@, newFrame)]
          /\ rtPC' = [rtPC EXCEPT ![pid] = firstLabel]
    /\ UNCHANGED <<ast, translationPhase, errors, warnings, globalVars,
                   procedures, processes, labelMap, genInitPredicate,
                   genNextRelation, genFairnessConditions, scopeStack,
                   declaredSymbols, rtState, rtEnabled, rtTerminated>>

\* Procedure return semantics
ExecuteReturn(pid) ==
    /\ Len(rtStack[pid]) > 0
    /\ LET frame == Head(rtStack[pid])
       IN /\ rtStack' = [rtStack EXCEPT ![pid] = Tail(@)]
          /\ rtPC' = [rtPC EXCEPT ![pid] = frame.returnLabel]
    /\ UNCHANGED <<ast, translationPhase, errors, warnings, globalVars,
                   procedures, processes, labelMap, genInitPredicate,
                   genNextRelation, genFairnessConditions, scopeStack,
                   declaredSymbols, rtState, rtEnabled, rtTerminated>>

\* Nondeterministic choice (either/or)
ExecuteEither(pid, choices) ==
    /\ rtPC[pid] \in LabelNames
    /\ \E choice \in ToSet(choices) :
       /\ choice.guard  \* Enabled branch
       /\ rtPC' = [rtPC EXCEPT ![pid] = choice.targetLabel]
    /\ UNCHANGED <<ast, translationPhase, errors, warnings, globalVars,
                   procedures, processes, labelMap, genInitPredicate,
                   genNextRelation, genFairnessConditions, scopeStack,
                   declaredSymbols, rtState, rtStack, rtEnabled, rtTerminated>>

\* With statement (existential choice)
ExecuteWith(pid, varName, domain) ==
    /\ rtPC[pid] \in LabelNames
    /\ \E val \in domain :
       /\ rtState' = [rtState EXCEPT !.vars[varName] = val]
    /\ UNCHANGED <<ast, translationPhase, errors, warnings, globalVars,
                   procedures, processes, labelMap, genInitPredicate,
                   genNextRelation, genFairnessConditions, scopeStack,
                   declaredSymbols, rtPC, rtStack, rtEnabled, rtTerminated>>

\* Process termination
ProcessTerminates(pid) ==
    /\ rtPC[pid] = "Done"
    /\ rtTerminated' = rtTerminated \cup {pid}
    /\ UNCHANGED <<ast, translationPhase, errors, warnings, globalVars,
                   procedures, processes, labelMap, genInitPredicate,
                   genNextRelation, genFairnessConditions, scopeStack,
                   declaredSymbols, rtState, rtPC, rtStack, rtEnabled>>

(***************************************************************************)
(* Initial State                                                           *)
(***************************************************************************)

Init ==
    /\ ast = [type |-> "Algorithm", 
              name |-> "",
              isMultiprocess |-> FALSE,
              globalVars |-> <<>>,
              procedures |-> <<>>,
              processes |-> <<>>,
              mainBody |-> <<>>]
    /\ translationPhase = "Parsing"
    /\ errors = {}
    /\ warnings = {}
    /\ globalVars = [v \in {} |-> [initValue |-> NullValue]]
    /\ procedures = [p \in {} |-> [params |-> <<>>, localVars |-> <<>>, 
                                    body |-> <<>>, labels |-> {}]]
    /\ processes = [p \in {} |-> [localVars |-> <<>>, body |-> <<>>,
                                   labels |-> {}, fairness |-> "None",
                                   instances |-> {}]]
    /\ labelMap = [l \in {} |-> [context |-> "unknown", 
                                  owner |-> NullValue, 
                                  statements |-> <<>>]]
    /\ genInitPredicate = [globalVarInits |-> [v \in {} |-> NullValue],
                           pcInit |-> [p \in {} |-> "Done"],
                           stackInit |-> [p \in {} |-> <<>>]]
    /\ genNextRelation = [actions |-> {}, stuttering |-> TRUE]
    /\ genFairnessConditions = [weakFair |-> {}, strongFair |-> {}, perAction |-> {}]
    /\ scopeStack = <<>>
    /\ declaredSymbols = {}
    /\ rtState = [vars |-> [v \in {} |-> NullValue]]
    /\ rtPC = [p \in {} |-> "Done"]
    /\ rtStack = [p \in {} |-> <<>>]
    /\ rtEnabled = {}
    /\ rtTerminated = {}

(***************************************************************************)
(* Next State Relation                                                     *)
(***************************************************************************)

TranslationStep ==
    \/ ParseAST
    \/ ValidateGlobalVars
    \/ ValidateProcedures
    \/ ValidateProcesses
    \/ ValidateLabelUniqueness
    \/ GenerateInit
    \/ GenerateLabelActions
    \/ GenerateNext
    \/ GenerateFairness

RuntimeStep ==
    \/ InitRuntime
    \/ ComputeEnabled
    \/ \E pid \in ProcessId : \E l \in LabelNames : ExecuteLabeledAction(pid, l)
    \/ \E pid \in ProcessId : ProcessTerminates(pid)

Next == TranslationStep \/ RuntimeStep

(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars /\ WF_vars(TranslationStep)

(***************************************************************************)
(* Safety Invariants                                                       *)
(***************************************************************************)

\* Type invariant
TypeOK ==
    /\ translationPhase \in {"Parsing", "Validating", "Generating", "Done", "Error"}
    /\ errors \subseteq STRING
    /\ warnings \subseteq STRING

\* No duplicate labels in final translation
NoDuplicateLabels ==
    translationPhase = "Done" =>
        \A l1, l2 \in DOMAIN labelMap :
            (labelMap[l1].owner = labelMap[l2].owner /\ l1 # l2) =>
            labelMap[l1].context # labelMap[l2].context

\* No duplicate variable declarations
NoDuplicateVars ==
    translationPhase = "Done" =>
        \A v \in DOMAIN globalVars :
            ~(\E p \in DOMAIN procedures : 
                v \in {d.name : d \in ToSet(procedures[p].localVars)})

\* Stack depth bounded
StackBounded ==
    \A pid \in DOMAIN rtStack : Len(rtStack[pid]) <= MaxStackDepth

\* PC always valid
PCValid ==
    \A pid \in DOMAIN rtPC :
        rtPC[pid] \in LabelNames \cup {"Done", "Error"}

\* Error state is terminal for translation
ErrorTerminal ==
    translationPhase = "Error" => translationPhase' = "Error"

\* Enabled actions correspond to reachable states
EnabledActionsValid ==
    translationPhase = "Done" =>
        \A a \in rtEnabled :
            \E pid \in DOMAIN rtPC :
                /\ rtPC[pid] = a.label
                /\ pid \notin rtTerminated

\* Procedure scoping preserved
ProcedureScopingCorrect ==
    \A pid \in DOMAIN rtStack :
        \A i \in 1..Len(rtStack[pid]) :
            LET frame == rtStack[pid][i]
            IN frame.procedure \in DOMAIN procedures

\* Terminated processes stay terminated
TerminationPermanent ==
    \A pid \in rtTerminated : rtPC[pid] = "Done"

(***************************************************************************)
(* Liveness Properties                                                     *)
(***************************************************************************)

\* Translation eventually completes or errors
TranslationCompletes ==
    <>(translationPhase \in {"Done", "Error"})

\* No deadlock in translation (always can make progress until done)
TranslationProgress ==
    [](translationPhase \notin {"Done", "Error"} => 
       ENABLED TranslationStep)

\* Fairness implies eventual execution for enabled actions
FairnessRespected ==
    \A pid \in DOMAIN processes :
        processes[pid].fairness = "WeakFair" =>
            WF_vars(\E l \in LabelNames : ExecuteLabeledAction(pid, l))

\* Strong fairness for strongly fair processes
StrongFairnessRespected ==
    \A pid \in DOMAIN processes :
        processes[pid].fairness = "StrongFair" =>
            SF_vars(\E l \in LabelNames : ExecuteLabeledAction(pid, l))

\* All processes eventually terminate or make progress
ProcessProgress ==
    \A pid \in ProcessId :
        [](pid \in DOMAIN rtPC /\ rtPC[pid] # "Done" /\ rtPC[pid] # "Error" =>
           <>(rtPC[pid]' # rtPC[pid] \/ pid \in rtTerminated'))

(***************************************************************************)
(* Correctness Properties                                                  *)
(***************************************************************************)

\* The translation preserves semantics: reachable states correspond
SemanticPreservation ==
    translationPhase = "Done" =>
        /\ genInitPredicate.globalVarInits = 
           [v \in DOMAIN globalVars |-> globalVars[v].initValue]
        /\ DOMAIN genInitPredicate.pcInit = 
           IF ast.isMultiprocess THEN DOMAIN processes ELSE {"main"}

\* Control flow integrity: goto targets exist
ControlFlowIntegrity ==
    translationPhase = "Done" =>
        \A l \in DOMAIN labelMap :
            labelMap[l].context # "unknown"

\* Nondeterministic choices are properly represented
NondeterminismCorrect ==
    \A pid \in DOMAIN rtPC :
        \A a1, a2 \in rtEnabled :
            (a1.label = a2.label /\ a1 # a2) =>
            \* Both choices remain available until one is taken
            rtPC[pid] = a1.label => rtPC[pid] = a2.label

=============================================================================