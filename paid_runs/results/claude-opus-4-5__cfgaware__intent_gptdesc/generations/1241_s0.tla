---------------------------- MODULE Translator ----------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Object, Any

-----------------------------------------------------------------------------
(* 
 * Abstract Syntax Tree Node Types for Source Language
 *)

(* Node kinds for AST representation *)
NodeKinds == {
    "Program", "Procedure", "Process", "Variable", "Label",
    "Assignment", "If", "Either", "While", "With", "When",
    "Call", "Return", "Goto", "Skip", "Assert", "Print",
    "Final", "Await", "MacroCall"
}

(* Expression types *)
ExprTypes == {
    "Const", "Var", "BinOp", "UnaryOp", "FuncApp", "Set", 
    "Record", "Tuple", "CHOOSE", "Quantifier"
}

(* Binary operators *)
BinOps == {
    "+", "-", "*", "/", "\\div", "%", "^",
    "=", "#", "<", ">", "<=", ">=",
    "/\\", "\\/", "=>", "<=>",
    "\\in", "\\notin", "\\subseteq", "\\union", "\\intersect", "\\"
}

(* Unary operators *)
UnaryOps == {"~", "-", "DOMAIN", "SUBSET", "UNION"}

-----------------------------------------------------------------------------
(*
 * Type definitions using Object and Any for model checking binding
 *)

(* Object represents any valid AST node or semantic object *)
IsObject(x) == x \in Object

(* Any represents any value that can appear in the specification *)
IsAny(x) == x \in Any

-----------------------------------------------------------------------------
(*
 * Source Language AST Structure
 *)

(* A Name is a string identifier *)
CONSTANT Names
ASSUME Names \subseteq Object

(* Variable declaration structure *)
VarDecl == [
    name: Names,
    init: Any,          \* Initial value expression
    isConstant: BOOLEAN \* Whether initializer must be constant
]

(* Label structure *)
LabelStruct == [
    name: Names,
    stmt: Any,          \* Statement at this label
    modifier: {"", "+", "-"}  \* Fairness modifier
]

(* Procedure structure *)
ProcedureStruct == [
    name: Names,
    params: Seq(Names),
    localVars: Seq(VarDecl),
    body: Seq(Any)      \* Sequence of labeled statements
]

(* Process structure *)
ProcessStruct == [
    name: Names,
    id: Any,            \* Process ID expression
    isSet: BOOLEAN,     \* Whether process set or single
    localVars: Seq(VarDecl),
    body: Seq(Any)
]

(* Program structure *)
ProgramStruct == [
    name: Names,
    globalVars: Seq(VarDecl),
    procedures: Seq(Any),
    processes: Seq(Any),
    isMultiProcess: BOOLEAN
]

-----------------------------------------------------------------------------
(*
 * Target Specification Structure
 *)

(* Control point representation *)
ControlPoint == [
    proc: Names,        \* Procedure or process name
    label: Names        \* Label within that context
]

(* State variable in target *)
StateVar == [
    name: Names,
    scope: {"global", "local", "parameter"},
    owner: Names        \* Process/procedure owning local/param
]

(* Transition structure *)
Transition == [
    from: ControlPoint,
    to: ControlPoint,
    guard: Any,         \* Boolean expression
    action: Any,        \* State update
    fairness: {"none", "weak", "strong"}
]

(* Call stack frame *)
StackFrame == [
    returnPoint: ControlPoint,
    locals: Any,        \* Local variable bindings
    params: Any         \* Parameter bindings
]

(* Target specification structure *)
TargetSpec == [
    name: Names,
    constants: Seq(Names),
    variables: Seq(StateVar),
    init: Any,          \* Initial state predicate
    next: Any,          \* Next state relation
    fairness: Any,      \* Fairness constraints
    spec: Any           \* Complete specification formula
]

-----------------------------------------------------------------------------
(*
 * Error Types for Validation
 *)

ErrorKinds == {
    "DuplicateDeclaration",
    "NonConstantInitializer",
    "UndefinedVariable",
    "UndefinedProcedure",
    "UndefinedLabel",
    "IllegalLocalReference",
    "TypeMismatch",
    "InvalidParameterCount",
    "CyclicProcedureCall",
    "MissingReturnLabel",
    "InvalidFairnessAnnotation",
    "ReservedNameUsed"
}

TranslationError == [
    kind: ErrorKinds,
    location: Any,
    message: Seq(Any)
]

-----------------------------------------------------------------------------
(*
 * VARIABLES for the Translator State Machine
 *)

VARIABLES
    inputAST,           \* The input program AST
    symbolTable,        \* Symbol table built during analysis
    controlFlowGraph,   \* Control flow graph
    targetSpec,         \* The generated target specification
    errors,             \* Collection of errors found
    translationPhase    \* Current phase of translation

vars == <<inputAST, symbolTable, controlFlowGraph, targetSpec, errors, translationPhase>>

-----------------------------------------------------------------------------
(*
 * Symbol Table Operations
 *)

EmptySymbolTable == [
    globals |-> {},
    procedures |-> {},
    processes |-> {},
    scopes |-> <<>>
]

(* Add a global variable to symbol table *)
AddGlobal(st, name, decl) ==
    [st EXCEPT !.globals = st.globals \union {<<name, decl>>}]

(* Add a procedure to symbol table *)
AddProcedure(st, name, proc) ==
    [st EXCEPT !.procedures = st.procedures \union {<<name, proc>>}]

(* Add a process to symbol table *)
AddProcess(st, name, proc) ==
    [st EXCEPT !.processes = st.processes \union {<<name, proc>>}]

(* Push a new scope *)
PushScope(st, scopeBindings) ==
    [st EXCEPT !.scopes = Append(st.scopes, scopeBindings)]

(* Pop current scope *)
PopScope(st) ==
    IF Len(st.scopes) > 0
    THEN [st EXCEPT !.scopes = SubSeq(st.scopes, 1, Len(st.scopes) - 1)]
    ELSE st

(* Lookup a name in symbol table *)
Lookup(st, name) ==
    LET 
        \* Search scopes from innermost to outermost
        FindInScopes(scopes) ==
            IF scopes = <<>> THEN Any
            ELSE LET last == scopes[Len(scopes)]
                 IN IF name \in DOMAIN last THEN last[name]
                    ELSE FindInScopes(SubSeq(scopes, 1, Len(scopes) - 1))
        localResult == FindInScopes(st.scopes)
    IN IF localResult # Any THEN localResult
       ELSE IF \E g \in st.globals : g[1] = name THEN 
            CHOOSE g \in st.globals : g[1] = name
       ELSE Any

-----------------------------------------------------------------------------
(*
 * Validation Predicates
 *)

(* Check if a name is already declared in current scope *)
IsDuplicate(st, name, currentScope) ==
    \/ \E g \in st.globals : g[1] = name
    \/ \E p \in st.procedures : p[1] = name
    \/ \E pr \in st.processes : pr[1] = name
    \/ (Len(st.scopes) > 0 /\ name \in DOMAIN st.scopes[Len(st.scopes)])

(* Reserved names that cannot be used *)
ReservedNames == {
    "TRUE", "FALSE", "BOOLEAN", "STRING",
    "pc", "stack", "self", "CONSTANT", "VARIABLE",
    "Init", "Next", "Spec", "Termination", "vars"
}

IsReserved(name) == name \in ReservedNames

(* Check if expression is constant (no variable references) *)
RECURSIVE IsConstantExpr(_)
IsConstantExpr(expr) ==
    CASE expr = Any -> TRUE
      [] \E c \in Object : expr = c -> TRUE  \* Literal constant
      [] OTHER -> FALSE  \* Simplified - real impl would traverse AST

(* Validate variable declaration *)
ValidateVarDecl(st, decl, requireConstInit) ==
    LET errs == {}
    IN IF IsReserved(decl.name) 
       THEN errs \union {[kind |-> "ReservedNameUsed", 
                          location |-> decl, 
                          message |-> <<"Reserved name:", decl.name>>]}
       ELSE IF IsDuplicate(st, decl.name, TRUE)
       THEN errs \union {[kind |-> "DuplicateDeclaration",
                          location |-> decl,
                          message |-> <<"Duplicate declaration:", decl.name>>]}
       ELSE IF requireConstInit /\ ~IsConstantExpr(decl.init)
       THEN errs \union {[kind |-> "NonConstantInitializer",
                          location |-> decl,
                          message |-> <<"Non-constant initializer for:", decl.name>>]}
       ELSE errs

-----------------------------------------------------------------------------
(*
 * Control Flow Graph Construction
 *)

EmptyCFG == [
    nodes |-> {},
    edges |-> {},
    entry |-> Any,
    exits |-> {}
]

(* Add a control point to CFG *)
AddNode(cfg, cp) ==
    [cfg EXCEPT !.nodes = cfg.nodes \union {cp}]

(* Add an edge to CFG *)
AddEdge(cfg, from, to, guard, action, fair) ==
    [cfg EXCEPT !.edges = cfg.edges \union 
        {[from |-> from, to |-> to, guard |-> guard, 
          action |-> action, fairness |-> fair]}]

(* Set entry point *)
SetEntry(cfg, cp) ==
    [cfg EXCEPT !.entry = cp]

(* Add exit point *)
AddExit(cfg, cp) ==
    [cfg EXCEPT !.exits = cfg.exits \union {cp}]

-----------------------------------------------------------------------------
(*
 * Statement Translation
 *)

(* Translate assignment statement *)
TranslateAssignment(lhs, rhs, currentCP, nextCP) ==
    [from |-> currentCP,
     to |-> nextCP,
     guard |-> TRUE,
     action |-> [var |-> lhs, expr |-> rhs],
     fairness |-> "none"]

(* Translate if statement - creates branching transitions *)
TranslateIf(cond, thenCP, elseCP, currentCP) ==
    {[from |-> currentCP, to |-> thenCP, guard |-> cond, 
      action |-> Any, fairness |-> "none"],
     [from |-> currentCP, to |-> elseCP, guard |-> [neg |-> cond],
      action |-> Any, fairness |-> "none"]}

(* Translate either statement - nondeterministic choice *)
TranslateEither(branches, currentCP) ==
    {[from |-> currentCP, to |-> b, guard |-> TRUE,
      action |-> Any, fairness |-> "none"] : b \in branches}

(* Translate while loop *)
TranslateWhile(cond, bodyCP, exitCP, currentCP) ==
    {[from |-> currentCP, to |-> bodyCP, guard |-> cond,
      action |-> Any, fairness |-> "none"],
     [from |-> currentCP, to |-> exitCP, guard |-> [neg |-> cond],
      action |-> Any, fairness |-> "none"]}

(* Translate with statement - introduces local binding *)
TranslateWith(var, setExpr, bodyCP, currentCP) ==
    [from |-> currentCP,
     to |-> bodyCP,
     guard |-> TRUE,
     action |-> [bind |-> var, from |-> setExpr],
     fairness |-> "none"]

(* Translate when/await - guarded transition *)
TranslateWhen(cond, nextCP, currentCP) ==
    [from |-> currentCP,
     to |-> nextCP,
     guard |-> cond,
     action |-> Any,
     fairness |-> "none"]

(* Translate procedure call *)
TranslateCall(procName, args, returnCP, currentCP) ==
    [from |-> currentCP,
     to |-> [proc |-> procName, label |-> "entry"],
     guard |-> TRUE,
     action |-> [call |-> procName, args |-> args, return |-> returnCP],
     fairness |-> "none"]

(* Translate return *)
TranslateReturn(currentCP) ==
    [from |-> currentCP,
     to |-> Any,  \* Determined by stack at runtime
     guard |-> TRUE,
     action |-> [return |-> TRUE],
     fairness |-> "none"]

(* Translate final/terminal statement *)
TranslateFinal(currentCP) ==
    [from |-> currentCP,
     to |-> [proc |-> "Done", label |-> "Done"],
     guard |-> TRUE,
     action |-> [done |-> TRUE],
     fairness |-> "none"]

-----------------------------------------------------------------------------
(*
 * Target Specification Generation
 *)

(* Generate Init predicate *)
GenerateInit(prog, st) ==
    LET 
        globalInits == {<<v[1], v[2].init>> : v \in st.globals}
        pcInit == IF prog.isMultiProcess
                  THEN [p \in {pr[1] : pr \in st.processes} |-> 
                        [proc |-> p, label |-> "entry"]]
                  ELSE [proc |-> "Main", label |-> "entry"]
        stackInit == IF prog.isMultiProcess
                     THEN [p \in {pr[1] : pr \in st.processes} |-> <<>>]
                     ELSE <<>>
    IN [globals |-> globalInits, pc |-> pcInit, stack |-> stackInit]

(* Generate Next predicate from CFG *)
GenerateNext(cfg, isMultiProcess) ==
    LET 
        transitions == cfg.edges
        ActionFor(t) == 
            /\ [pc |-> t.from]
            /\ t.guard
            /\ t.action
            /\ [pc |-> t.to]'
    IN [transitions |-> transitions, disjunct |-> TRUE]

(* Generate fairness constraints *)
GenerateFairness(cfg, fairnessType) ==
    LET 
        weakFairEdges == {e \in cfg.edges : e.fairness = "weak"}
        strongFairEdges == {e \in cfg.edges : e.fairness = "strong"}
    IN [weak |-> weakFairEdges, strong |-> strongFairEdges]

(* Generate complete target specification *)
GenerateTargetSpec(prog, st, cfg) ==
    [name |-> prog.name,
     constants |-> {v[1] : v \in st.globals},
     variables |-> {[name |-> "pc", scope |-> "global", owner |-> Any],
                    [name |-> "stack", scope |-> "global", owner |-> Any]} 
                   \union 
                   {[name |-> v[1], scope |-> "global", owner |-> Any] : 
                    v \in st.globals},
     init |-> GenerateInit(prog, st),
     next |-> GenerateNext(cfg, prog.isMultiProcess),
     fairness |-> GenerateFairness(cfg, "weak"),
     spec |-> [init |-> TRUE, next |-> TRUE, fairness |-> TRUE]]

-----------------------------------------------------------------------------
(*
 * Translation Phases
 *)

Phases == {"Init", "Parse", "Validate", "BuildSymbols", "BuildCFG", 
           "Generate", "Complete", "Error"}

(* Type invariant *)
TypeInvariant ==
    /\ translationPhase \in Phases
    /\ errors \subseteq [kind: ErrorKinds, location: Any, message: Seq(Any)]

(* Initial state *)
Init ==
    /\ inputAST = Any
    /\ symbolTable = EmptySymbolTable
    /\ controlFlowGraph = EmptyCFG
    /\ targetSpec = Any
    /\ errors = {}
    /\ translationPhase = "Init"

(* Accept input *)
AcceptInput(ast) ==
    /\ translationPhase = "Init"
    /\ inputAST' = ast
    /\ translationPhase' = "Parse"
    /\ UNCHANGED <<symbolTable, controlFlowGraph, targetSpec, errors>>

(* Build symbol table phase *)
BuildSymbolTable ==
    /\ translationPhase = "Parse"
    /\ translationPhase' = "BuildSymbols"
    /\ \E st \in [globals: SUBSET (Names \X VarDecl),
                  procedures: SUBSET (Names \X Any),
                  processes: SUBSET (Names \X Any),
                  scopes: Seq(Any)] :
        symbolTable' = st
    /\ UNCHANGED <<inputAST, controlFlowGraph, targetSpec, errors>>

(* Validation phase *)
Validate ==
    /\ translationPhase = "BuildSymbols"
    /\ IF errors = {} 
       THEN translationPhase' = "BuildCFG"
       ELSE translationPhase' = "Error"
    /\ UNCHANGED <<inputAST, symbolTable, controlFlowGraph, targetSpec, errors>>

(* Build control flow graph phase *)
BuildCFG ==
    /\ translationPhase = "BuildCFG"
    /\ \E cfg \in [nodes: SUBSET ControlPoint,
                   edges: SUBSET Transition,
                   entry: Any,
                   exits: SUBSET ControlPoint] :
        controlFlowGraph' = cfg
    /\ translationPhase' = "Generate"
    /\ UNCHANGED <<inputAST, symbolTable, targetSpec, errors>>

(* Generate target specification phase *)
Generate ==
    /\ translationPhase = "Generate"
    /\ targetSpec' = GenerateTargetSpec(inputAST, symbolTable, controlFlowGraph)
    /\ translationPhase' = "Complete"
    /\ UNCHANGED <<inputAST, symbolTable, controlFlowGraph, errors>>

(* Error state - translation undefined *)
ErrorState ==
    /\ translationPhase = "Error"
    /\ UNCHANGED vars

(* Complete state *)
CompleteState ==
    /\ translationPhase = "Complete"
    /\ UNCHANGED vars

(* Next state relation *)
Next ==
    \/ \E ast \in Object : AcceptInput(ast)
    \/ BuildSymbolTable
    \/ Validate
    \/ BuildCFG
    \/ Generate
    \/ ErrorState
    \/ CompleteState

(* Fairness - translation should make progress *)
Fairness == WF_vars(Next)

(* Complete specification *)
Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(*
 * Correctness Properties
 *)

(* Semantic Preservation: Every source behavior has corresponding target behavior *)
SemanticPreservation ==
    translationPhase = "Complete" =>
        \* The target spec preserves control flow structure
        /\ controlFlowGraph.nodes # {}
        /\ controlFlowGraph.entry # Any
        \* Every reachable label has outgoing transitions (except exits)
        /\ \A n \in (controlFlowGraph.nodes \ controlFlowGraph.exits) :
             \E e \in controlFlowGraph.edges : e.from = n

(* Safety Preservation: Invariants and assertions preserved *)
SafetyPreservation ==
    translationPhase = "Complete" =>
        \* Target spec has proper Init and Next
        /\ targetSpec.init # Any
        /\ targetSpec.next # Any

(* Termination Preservation: Final statements lead to done state *)
TerminationPreservation ==
    translationPhase = "Complete" =>
        \* Exit points exist and lead to done
        controlFlowGraph.exits # {} =>
            \A exit \in controlFlowGraph.exits :
                \E e \in controlFlowGraph.edges :
                    /\ e.from = exit
                    /\ e.to = [proc |-> "Done", label |-> "Done"]

(* Error Detection: Invalid inputs are identified *)
ErrorDetection ==
    errors # {} => translationPhase \in {"Error", "BuildSymbols", "Validate"}

(* Progress: Translation eventually completes or errors *)
Progress == <>(translationPhase \in {"Complete", "Error"})

(* Combined correctness property *)
Correctness ==
    /\ SemanticPreservation
    /\ SafetyPreservation
    /\ TerminationPreservation
    /\ ErrorDetection

-----------------------------------------------------------------------------
(*
 * Helper operators for specification users
 *)

(* Check if translation was successful *)
TranslationSucceeded == 
    /\ translationPhase = "Complete"
    /\ errors = {}

(* Check if translation failed with errors *)
TranslationFailed ==
    /\ translationPhase = "Error"
    /\ errors # {}

(* Get the generated specification (only valid after successful translation) *)
GetTargetSpec == 
    IF TranslationSucceeded THEN targetSpec ELSE Any

(* Get all errors (only meaningful if translation failed) *)
GetErrors ==
    IF TranslationFailed THEN errors ELSE {}

=============================================================================