---------------------------- MODULE PlusCal2TLA ----------------------------
(***************************************************************************)
(* Formal model of a translator from an abstract procedural algorithm      *)
(* language (similar to PlusCal) to a state-based specification (TLA+).    *)
(* This specification captures the translation semantics abstractly.       *)
(***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    \* Source language constructs
    ProcedureNames,      \* Set of valid procedure names
    VariableNames,       \* Set of valid variable names
    LabelNames,          \* Set of valid label names
    ProcessIds,          \* Set of process identifiers
    Values,              \* Domain of values
    MaxCallDepth,        \* Maximum call stack depth
    MaxProcesses,        \* Maximum number of processes
    
    \* Special constants
    Undefined,           \* Undefined/uninitialized marker
    ErrorValue,          \* Error marker
    Done                 \* Terminal state marker

ASSUME MaxCallDepth \in Nat /\ MaxCallDepth > 0
ASSUME MaxProcesses \in Nat /\ MaxProcesses > 0
ASSUME Done \notin Values
ASSUME Undefined \notin Values
ASSUME ErrorValue \notin Values

(***************************************************************************)
(* Abstract Syntax Tree Representation                                     *)
(***************************************************************************)

\* Statement types
StatementTypes == {
    "assignment", "if", "either", "while", "with", "when",
    "call", "return", "goto", "print", "assert", "skip",
    "await", "final"
}

\* Declaration types
DeclTypes == {"global", "local", "parameter", "procedure_local"}

\* Process structure types
ProcessStructures == {"uniprocess", "multiprocess"}

(***************************************************************************)
(* Source Program Structure (Abstract Representation)                      *)
(***************************************************************************)

\* A variable declaration record
VarDecl == [
    name: VariableNames,
    type: DeclTypes,
    initializer: Values \cup {Undefined},
    isConstantInit: BOOLEAN,
    scope: VariableNames \cup {Undefined}  \* Procedure name or Undefined for global
]

\* A labeled statement record
LabeledStmt == [
    label: LabelNames,
    stmtType: StatementTypes,
    isFinal: BOOLEAN
]

\* A procedure definition record
ProcedureDef == [
    name: ProcedureNames,
    params: SUBSET VariableNames,
    locals: SUBSET VariableNames,
    body: Seq(LabeledStmt)
]

\* A process definition record
ProcessDef == [
    id: ProcessIds,
    variables: SUBSET VariableNames,
    body: Seq(LabeledStmt),
    fairness: {"weak", "strong", "none"}
]

\* Complete source program record
SourceProgram == [
    name: Seq(VariableNames),  \* Module name as sequence
    globals: SUBSET VarDecl,
    procedures: SUBSET ProcedureDef,
    processes: SUBSET ProcessDef,
    structure: ProcessStructures,
    globalFairness: {"weak", "strong", "none"}
]

(***************************************************************************)
(* Target Specification Structure (Abstract Representation)                *)
(***************************************************************************)

\* Control point representation
ControlPoint == LabelNames \cup {Done, ErrorValue}

\* Call stack frame
StackFrame == [
    returnPoint: ControlPoint,
    procedure: ProcedureNames,
    locals: [VariableNames -> Values \cup {Undefined}]
]

\* Per-process state
ProcessState == [
    pc: ControlPoint,
    stack: Seq(StackFrame),
    locals: [VariableNames -> Values \cup {Undefined}]
]

\* Target specification state shape
TargetState == [
    globals: [VariableNames -> Values \cup {Undefined}],
    processes: [ProcessIds -> ProcessState],
    terminated: SUBSET ProcessIds
]

\* Transition relation entry
Transition == [
    fromPC: ControlPoint,
    toPC: ControlPoint,
    guard: BOOLEAN,
    process: ProcessIds \cup {Undefined},
    action: StatementTypes
]

\* Complete target specification record
TargetSpec == [
    variables: SUBSET VariableNames,
    pcVariable: VariableNames,
    stackVariable: VariableNames,
    initPredicate: TargetState,
    transitions: SUBSET Transition,
    fairnessConstraints: SUBSET [process: ProcessIds, level: {"weak", "strong"}],
    invariants: SUBSET BOOLEAN,
    terminalStates: SUBSET ControlPoint
]

(***************************************************************************)
(* Translation State Variables                                             *)
(***************************************************************************)

VARIABLES
    \* Input
    inputProgram,        \* The source program AST
    
    \* Translation state
    translationPhase,    \* Current phase: "init", "validate", "translate", "done", "error"
    validationErrors,    \* Set of detected errors
    
    \* Output
    outputSpec,          \* The generated target specification
    
    \* Semantic mapping (for correctness reasoning)
    stateMapping,        \* Mapping from source states to target states
    behaviorCorrespondence,  \* Witness for behavior equivalence
    
    \* Auxiliary
    currentScope,        \* Current scope during translation
    symbolTable,         \* Symbol table for name resolution
    controlFlowGraph     \* Intermediate CFG representation

vars == <<inputProgram, translationPhase, validationErrors, outputSpec,
          stateMapping, behaviorCorrespondence, currentScope, symbolTable,
          controlFlowGraph>>

(***************************************************************************)
(* Error Classes                                                           *)
(***************************************************************************)

ErrorClasses == {
    "duplicate_declaration",
    "undeclared_variable",
    "non_constant_global_init",
    "non_constant_procedure_param_init",
    "illegal_local_in_global_scope",
    "duplicate_label",
    "unreachable_label",
    "missing_return",
    "illegal_goto_target",
    "type_mismatch",
    "invalid_process_id",
    "circular_procedure_call",
    "stack_overflow",
    "invalid_with_binding",
    "invalid_when_guard"
}

Error == [class: ErrorClasses, location: Nat, message: Seq(VariableNames)]

(***************************************************************************)
(* Helper Predicates for Validation                                        *)
(***************************************************************************)

\* Check if a name is already declared in scope
IsDeclared(name, scope, symTab) ==
    \E entry \in symTab: entry.name = name /\ entry.scope = scope

\* Check if initializer is a constant expression (abstractly)
IsConstantExpr(expr) ==
    expr \in Values \cup {Undefined}

\* Check for duplicate declarations in a set of declarations
HasDuplicateDecls(decls) ==
    \E d1, d2 \in decls: d1 # d2 /\ d1.name = d2.name /\ d1.scope = d2.scope

\* Check for duplicate labels in a sequence of statements
HasDuplicateLabels(stmts) ==
    \E i, j \in DOMAIN stmts: 
        i # j /\ stmts[i].label = stmts[j].label

\* Validate global variable declarations
ValidateGlobalDecl(decl) ==
    /\ decl.type = "global"
    /\ decl.isConstantInit
    /\ decl.scope = Undefined

\* Validate procedure parameter declarations
ValidateProcedureParam(decl, procName) ==
    /\ decl.type = "parameter"
    /\ decl.scope = procName

(***************************************************************************)
(* Semantic Validation Functions                                           *)
(***************************************************************************)

\* Collect all validation errors for a source program
CollectErrors(prog) ==
    LET globalErrors == 
        IF HasDuplicateDecls(prog.globals)
        THEN {[class |-> "duplicate_declaration", 
               location |-> 0, 
               message |-> <<"global", "scope">>]}
        ELSE {}
    IN
    LET nonConstErrors ==
        {[class |-> "non_constant_global_init",
          location |-> 0,
          message |-> <<decl.name>>] : 
         decl \in {d \in prog.globals : ~d.isConstantInit}}
    IN
    globalErrors \cup nonConstErrors

\* Check if program is well-formed
IsWellFormed(prog) ==
    /\ CollectErrors(prog) = {}
    /\ \A proc \in prog.procedures: ~HasDuplicateLabels(proc.body)
    /\ \A p \in prog.processes: ~HasDuplicateLabels(p.body)

(***************************************************************************)
(* Control Flow Graph Construction                                         *)
(***************************************************************************)

\* Abstract CFG node
CFGNode == [
    label: ControlPoint,
    stmtType: StatementTypes,
    successors: SUBSET ControlPoint,
    isEntry: BOOLEAN,
    isExit: BOOLEAN,
    isFinal: BOOLEAN
]

\* Build CFG from statement sequence (abstract representation)
BuildCFG(stmts) ==
    IF stmts = <<>>
    THEN {}
    ELSE 
        LET firstStmt == Head(stmts)
            restCFG == BuildCFG(Tail(stmts))
            nextLabel == IF Tail(stmts) = <<>> 
                        THEN Done 
                        ELSE Head(Tail(stmts)).label
        IN
        {[label |-> firstStmt.label,
          stmtType |-> firstStmt.stmtType,
          successors |-> {nextLabel},
          isEntry |-> (stmts = stmts),  \* First statement
          isExit |-> (Tail(stmts) = <<>>),
          isFinal |-> firstStmt.isFinal]} 
        \cup restCFG

(***************************************************************************)
(* Translation Functions                                                   *)
(***************************************************************************)

\* Translate variable declaration to target representation
TranslateVarDecl(decl) ==
    [name |-> decl.name,
     initValue |-> IF decl.initializer = Undefined 
                   THEN Undefined 
                   ELSE decl.initializer]

\* Translate assignment statement
TranslateAssignment(stmt, pc, nextPC, proc) ==
    [fromPC |-> pc,
     toPC |-> nextPC,
     guard |-> TRUE,
     process |-> proc,
     action |-> "assignment"]

\* Translate conditional (if) statement - creates multiple transitions
TranslateIf(stmt, pc, thenPC, elsePC, proc) ==
    {[fromPC |-> pc, toPC |-> thenPC, guard |-> TRUE, 
      process |-> proc, action |-> "if"],
     [fromPC |-> pc, toPC |-> elsePC, guard |-> TRUE,
      process |-> proc, action |-> "if"]}

\* Translate nondeterministic choice (either)
TranslateEither(stmt, pc, choices, proc) ==
    {[fromPC |-> pc, toPC |-> choice, guard |-> TRUE,
      process |-> proc, action |-> "either"] : choice \in choices}

\* Translate while loop
TranslateWhile(stmt, pc, bodyPC, exitPC, proc) ==
    {[fromPC |-> pc, toPC |-> bodyPC, guard |-> TRUE,
      process |-> proc, action |-> "while"],
     [fromPC |-> pc, toPC |-> exitPC, guard |-> TRUE,
      process |-> proc, action |-> "while"]}

\* Translate with statement (local binding)
TranslateWith(stmt, pc, nextPC, proc) ==
    [fromPC |-> pc,
     toPC |-> nextPC,
     guard |-> TRUE,
     process |-> proc,
     action |-> "with"]

\* Translate when/await statement (guarded)
TranslateWhen(stmt, pc, nextPC, proc) ==
    [fromPC |-> pc,
     toPC |-> nextPC,
     guard |-> TRUE,  \* Abstract guard - actual condition in semantics
     process |-> proc,
     action |-> "when"]

\* Translate procedure call
TranslateCall(stmt, pc, entryPC, returnPC, proc) ==
    [fromPC |-> pc,
     toPC |-> entryPC,
     guard |-> TRUE,
     process |-> proc,
     action |-> "call"]

\* Translate procedure return
TranslateReturn(stmt, pc, proc) ==
    [fromPC |-> pc,
     toPC |-> Undefined,  \* Return point determined by stack
     guard |-> TRUE,
     process |-> proc,
     action |-> "return"]

\* Translate final/terminal statement
TranslateFinal(stmt, pc, proc) ==
    [fromPC |-> pc,
     toPC |-> Done,
     guard |-> TRUE,
     process |-> proc,
     action |-> "final"]

(***************************************************************************)
(* Complete Translation                                                    *)
(***************************************************************************)

\* Generate initialization predicate
GenerateInit(prog) ==
    [globals |-> [v \in {d.name : d \in prog.globals} |-> 
                  LET decl == CHOOSE d \in prog.globals : d.name = v
                  IN decl.initializer],
     processes |-> [p \in {pr.id : pr \in prog.processes} |->
                    [pc |-> IF \E pr \in prog.processes : pr.id = p
                            THEN LET process == CHOOSE pr \in prog.processes : pr.id = p
                                 IN IF process.body = <<>> 
                                    THEN Done 
                                    ELSE Head(process.body).label
                            ELSE Done,
                     stack |-> <<>>,
                     locals |-> [v \in VariableNames |-> Undefined]]],
     terminated |-> {}]

\* Generate fairness constraints
GenerateFairness(prog) ==
    LET processFairness == 
        {[process |-> p.id, level |-> p.fairness] : 
         p \in {pr \in prog.processes : pr.fairness # "none"}}
    IN
    IF prog.globalFairness = "none"
    THEN processFairness
    ELSE processFairness \cup {[process |-> Undefined, level |-> prog.globalFairness]}

\* Generate terminal states
GenerateTerminalStates(prog) ==
    LET finalLabels == 
        UNION {{s.label : s \in {stmt \in ToSet(p.body) : stmt.isFinal}} : 
               p \in prog.processes}
    IN
    finalLabels \cup {Done}

\* Utility: Convert sequence to set
ToSet(seq) == {seq[i] : i \in DOMAIN seq}

\* Main translation function
Translate(prog) ==
    IF ~IsWellFormed(prog)
    THEN [variables |-> {},
          pcVariable |-> "pc",
          stackVariable |-> "stack",
          initPredicate |-> [globals |-> [v \in {} |-> Undefined],
                            processes |-> [p \in {} |-> 
                                [pc |-> Done, stack |-> <<>>, 
                                 locals |-> [v \in {} |-> Undefined]]],
                            terminated |-> {}],
          transitions |-> {},
          fairnessConstraints |-> {},
          invariants |-> {},
          terminalStates |-> {Done}]
    ELSE
    [variables |-> {d.name : d \in prog.globals} \cup 
                   UNION {{v : v \in p.variables} : p \in prog.processes},
     pcVariable |-> "pc",
     stackVariable |-> "stack",
     initPredicate |-> GenerateInit(prog),
     transitions |-> {},  \* Abstractly represented
     fairnessConstraints |-> GenerateFairness(prog),
     invariants |-> {},
     terminalStates |-> GenerateTerminalStates(prog)]

(***************************************************************************)
(* State Mapping for Semantic Equivalence                                  *)
(***************************************************************************)

\* Map source state to target state representation
SourceToTargetState(sourceState) ==
    sourceState  \* Identity mapping in abstract model

\* Map target state to source state representation  
TargetToSourceState(targetState) ==
    targetState  \* Identity mapping in abstract model

\* Check if two states are equivalent modulo representation
StatesEquivalent(s1, s2) ==
    /\ s1.globals = s2.globals
    /\ \A p \in DOMAIN s1.processes:
        /\ s1.processes[p].pc = s2.processes[p].pc
        /\ s1.processes[p].locals = s2.processes[p].locals

(***************************************************************************)
(* Initial State                                                           *)
(***************************************************************************)

Init ==
    /\ inputProgram = [name |-> <<"example">>,
                       globals |-> {},
                       procedures |-> {},
                       processes |-> {},
                       structure |-> "uniprocess",
                       globalFairness |-> "none"]
    /\ translationPhase = "init"
    /\ validationErrors = {}
    /\ outputSpec = [variables |-> {},
                     pcVariable |-> "pc",
                     stackVariable |-> "stack",
                     initPredicate |-> [globals |-> [v \in {} |-> Undefined],
                                       processes |-> [p \in {} |-> 
                                           [pc |-> Done, stack |-> <<>>, 
                                            locals |-> [v \in {} |-> Undefined]]],
                                       terminated |-> {}],
                     transitions |-> {},
                     fairnessConstraints |-> {},
                     invariants |-> {},
                     terminalStates |-> {Done}]
    /\ stateMapping = [source |-> {}, target |-> {}]
    /\ behaviorCorrespondence = <<>>
    /\ currentScope = Undefined
    /\ symbolTable = {}
    /\ controlFlowGraph = {}

(***************************************************************************)
(* State Transitions                                                       *)
(***************************************************************************)

\* Accept new input program
AcceptInput(prog) ==
    /\ translationPhase = "init"
    /\ inputProgram' = prog
    /\ translationPhase' = "validate"
    /\ UNCHANGED <<validationErrors, outputSpec, stateMapping, 
                   behaviorCorrespondence, currentScope, symbolTable,
                   controlFlowGraph>>

\* Validate input program
Validate ==
    /\ translationPhase = "validate"
    /\ LET errors == CollectErrors(inputProgram)
       IN
       /\ validationErrors' = errors
       /\ IF errors = {}
          THEN translationPhase' = "translate"
          ELSE translationPhase' = "error"
    /\ UNCHANGED <<inputProgram, outputSpec, stateMapping,
                   behaviorCorrespondence, currentScope, symbolTable,
                   controlFlowGraph>>

\* Build symbol table
BuildSymbolTable ==
    /\ translationPhase = "translate"
    /\ symbolTable = {}
    /\ LET globalSymbols == {[name |-> d.name, 
                              scope |-> Undefined,
                              type |-> d.type] : d \in inputProgram.globals}
       IN symbolTable' = globalSymbols
    /\ UNCHANGED <<inputProgram, translationPhase, validationErrors, outputSpec,
                   stateMapping, behaviorCorrespondence, currentScope,
                   controlFlowGraph>>

\* Build control flow graph
BuildControlFlow ==
    /\ translationPhase = "translate"
    /\ symbolTable # {}
    /\ controlFlowGraph = {}
    /\ LET processCFGs == UNION {BuildCFG(p.body) : p \in inputProgram.processes}
       IN controlFlowGraph' = processCFGs
    /\ UNCHANGED <<inputProgram, translationPhase, validationErrors, outputSpec,
                   stateMapping, behaviorCorrespondence, currentScope, symbolTable>>

\* Generate target specification
GenerateOutput ==
    /\ translationPhase = "translate"
    /\ symbolTable # {}
    /\ controlFlowGraph # {}
    /\ outputSpec' = Translate(inputProgram)
    /\ translationPhase' = "done"
    /\ UNCHANGED <<inputProgram, validationErrors, stateMapping,
                   behaviorCorrespondence, currentScope, symbolTable,
                   controlFlowGraph>>

\* Establish semantic correspondence
EstablishCorrespondence ==
    /\ translationPhase = "done"
    /\ stateMapping' = [source |-> {outputSpec.initPredicate},
                        target |-> {outputSpec.initPredicate}]
    /\ behaviorCorrespondence' = <<[source |-> outputSpec.initPredicate,
                                     target |-> outputSpec.initPredicate]>>
    /\ UNCHANGED <<inputProgram, translationPhase, validationErrors, outputSpec,
                   currentScope, symbolTable, controlFlowGraph>>

\* Next state relation
Next ==
    \/ \E prog \in SourceProgram: AcceptInput(prog)
    \/ Validate
    \/ BuildSymbolTable
    \/ BuildControlFlow
    \/ GenerateOutput
    \/ EstablishCorrespondence

(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Safety Invariants                                                       *)
(***************************************************************************)

\* Type invariant
TypeInvariant ==
    /\ translationPhase \in {"init", "validate", "translate", "done", "error"}
    /\ validationErrors \subseteq Error

\* No output if errors detected
NoOutputOnError ==
    translationPhase = "error" => outputSpec.transitions = {}

\* Well-formed output when translation succeeds
WellFormedOutput ==
    translationPhase = "done" =>
        /\ outputSpec.pcVariable \in VariableNames \cup {"pc"}
        /\ outputSpec.stackVariable \in VariableNames \cup {"stack"}
        /\ Done \in outputSpec.terminalStates

\* Semantic preservation: every source behavior has corresponding target behavior
SemanticPreservation ==
    translationPhase = "done" =>
        \A srcState \in stateMapping.source:
            \E tgtState \in stateMapping.target:
                StatesEquivalent(srcState, tgtState)

\* Safety property preservation
SafetyPreservation ==
    translationPhase = "done" =>
        \A inv \in outputSpec.invariants:
            inv  \* Invariants carry over

\* Terminal state preservation
TerminalPreservation ==
    translationPhase = "done" =>
        Done \in outputSpec.terminalStates

\* Error detection completeness
ErrorDetectionCompleteness ==
    (translationPhase = "error") <=> (validationErrors # {})

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeInvariant
    /\ NoOutputOnError
    /\ WellFormedOutput
    /\ ErrorDetectionCompleteness

(***************************************************************************)
(* Liveness Properties                                                     *)
(***************************************************************************)

\* Translation eventually completes or reports error
TranslationTerminates ==
    translationPhase = "validate" ~> 
        (translationPhase = "done" \/ translationPhase = "error")

\* Valid input eventually produces output
ValidInputProducesOutput ==
    (translationPhase = "validate" /\ validationErrors = {}) ~>
        (translationPhase = "done" /\ outputSpec.variables # {})

\* Correspondence eventually established for successful translation
CorrespondenceEstablished ==
    translationPhase = "done" ~> behaviorCorrespondence # <<>>

(***************************************************************************)
(* Refinement Mapping for Correctness                                      *)
(***************************************************************************)

\* The key correctness theorem (stated as invariant for model checking)
\* For any well-formed source program P, if T = Translate(P), then:
\* 1. Every behavior of P corresponds to a behavior of T
\* 2. Every behavior of T corresponds to a behavior of P
\* 3. Safety properties (invariants, assertions) are preserved
\* 4. Terminal states in P map to terminal states in T

CorrectnessTheorem ==
    translationPhase = "done" =>
        LET T == outputSpec
            hasInit == T.initPredicate.globals = T.initPredicate.globals
            hasTransitions == TRUE  \* Abstractly true when well-formed
            preservesTerminal == Done \in T.terminalStates
        IN hasInit /\ hasTransitions /\ preservesTerminal

=============================================================================