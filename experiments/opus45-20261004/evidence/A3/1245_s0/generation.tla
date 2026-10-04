---------------------------- MODULE PlusCalToTLA ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    MaxProcesses,
    MaxStatements,
    MaxVariables,
    MaxExprDepth

VARIABLES
    ast,
    tlaPlusSpec,
    translationPhase,
    processedStatements,
    localVarSubscripts,
    fairnessOption,
    errors

vars == <<ast, tlaPlusSpec, translationPhase, processedStatements, localVarSubscripts, fairnessOption, errors>>

-----------------------------------------------------------------------------
(* Fairness Options *)
NoFairness == 0
WeakFairnessOfProcessActions == 1
WeakFairnessOfNext == 2
StrongFairnessOfProcessActions == 3

FairnessOptions == {NoFairness, WeakFairnessOfProcessActions, WeakFairnessOfNext, StrongFairnessOfProcessActions}

-----------------------------------------------------------------------------
(* Abstract Syntax Tree Grammar - Definitions as Sets and Predicates *)

(* Identifiers are strings represented as sequences of characters *)
Identifiers == STRING

(* Expression types in the AST *)
ExprTypes == {"literal", "variable", "operator", "function_call", "set", "sequence", "record"}

(* A predicate to check if something is a valid expression *)
IsExpression(e) ==
    /\ e \in [type: ExprTypes, value: STRING]
    \/ e \in [type: {"operator"}, op: STRING, args: Seq([type: ExprTypes, value: STRING])]

(* Statement types in the AST *)
StatementTypes == {
    "assignment",
    "if",
    "while", 
    "either",
    "with",
    "await",
    "print",
    "assert",
    "skip",
    "call",
    "return",
    "goto",
    "labeled"
}

(* Variable declaration structure *)
VarDecls == [name: Identifiers, initialValue: STRING, isConstant: BOOLEAN]

(* Statement structure - simplified representation *)
Statements == [
    type: StatementTypes,
    label: Identifiers \cup {""}, 
    target: Identifiers \cup {""},
    expr: STRING,
    body: Seq(Nat),
    elseBody: Seq(Nat)
]

(* Process structure *)
Processes == [
    name: Identifiers,
    id: Nat,
    variables: Seq(VarDecls),
    statements: Seq(Nat),
    isMultiProcess: BOOLEAN
]

(* Algorithm structure - the root of the AST *)
Algorithms == [
    name: Identifiers,
    globalVariables: Seq(VarDecls),
    processes: Seq(Nat),
    definitions: Seq(STRING),
    macros: Seq(STRING)
]

(* Translation phases *)
TranslationPhases == {
    "initial",
    "explode_labels",
    "translate_calls_returns_gotos",
    "add_var_subscripts",
    "construct_init",
    "construct_next",
    "construct_spec",
    "construct_termination",
    "complete"
}

-----------------------------------------------------------------------------
(* TLA+ Specification Output Structure *)

TLAPlusSpecs == [
    moduleName: Identifiers,
    extends: Seq(STRING),
    constants: Seq(STRING),
    variables: Seq(STRING),
    init: STRING,
    next: STRING,
    spec: STRING,
    termination: STRING,
    fairness: STRING,
    processActions: Seq(STRING),
    auxiliaryDefs: Seq(STRING)
]

-----------------------------------------------------------------------------
(* Helper Operators *)

EmptyAST == [
    name |-> "",
    globalVariables |-> <<>>,
    processes |-> <<>>,
    definitions |-> <<>>,
    macros |-> <<>>
]

EmptyTLASpec == [
    moduleName |-> "",
    extends |-> <<>>,
    constants |-> <<>>,
    variables |-> <<>>,
    init |-> "",
    next |-> "",
    spec |-> "",
    termination |-> "",
    fairness |-> "",
    processActions |-> <<>>,
    auxiliaryDefs |-> <<>>
]

(* Check if AST is valid *)
IsValidAST(a) ==
    /\ a.name \in Identifiers
    /\ Len(a.processes) <= MaxProcesses

(* Get all variable names from AST *)
GetAllVariables(a) ==
    LET globals == {a.globalVariables[i].name : i \in 1..Len(a.globalVariables)}
    IN globals

(* Check if a statement has a label *)
HasLabel(stmt) == stmt.label # ""

(* Count labeled statements *)
CountLabeledStatements(stmts) ==
    Cardinality({i \in 1..Len(stmts) : stmts[i].label # ""})

-----------------------------------------------------------------------------
(* Translation Pipeline Operators *)

(* Phase 1: Explode structured labeled statements *)
(* This phase breaks down compound statements with labels into atomic labeled actions *)
ExplodeLabeledStatements(statements) ==
    statements

(* Phase 2: Translate calls, returns, and gotos *)
(* Converts PlusCal control flow to TLA+ state machine transitions *)
TranslateCallsReturnsGotos(statements) ==
    statements

(* Phase 3: Add subscripts for process-local variables *)
(* Converts local variables to arrays indexed by process id: var becomes var[self] *)
AddVarSubscripts(statements, processId) ==
    statements

(* Phase 4: Construct Init predicate *)
(* Initializes all variables including pc (program counter) *)
ConstructInit(a) ==
    LET varInits == "TRUE"
        pcInit == "pc = \"init\""
    IN "Init == " \o varInits \o " /\\ " \o pcInit

(* Phase 5: Construct Next relation *)
(* Disjunction of all process actions *)
ConstructNext(a, processActions) ==
    IF Len(processActions) = 0 
    THEN "Next == FALSE"
    ELSE "Next == \\E self \\in ProcSet: " \o processActions[1]

(* Phase 6: Construct Spec with fairness *)
ConstructSpec(initDef, nextDef, fairOpt) ==
    LET base == "Spec == Init /\\ [][Next]_vars"
        fairness == CASE fairOpt = NoFairness -> ""
                     [] fairOpt = WeakFairnessOfNext -> " /\\ WF_vars(Next)"
                     [] fairOpt = WeakFairnessOfProcessActions -> " /\\ \\A self \\in ProcSet: WF_vars(proc(self))"
                     [] fairOpt = StrongFairnessOfProcessActions -> " /\\ \\A self \\in ProcSet: SF_vars(proc(self))"
                     [] OTHER -> ""
    IN base \o fairness

(* Phase 7: Construct Termination property *)
ConstructTermination ==
    "Termination == <>(\\A self \\in ProcSet: pc[self] = \"Done\")"

-----------------------------------------------------------------------------
(* State Transitions *)

(* Initialize the translation *)
InitTranslation ==
    /\ ast' = EmptyAST
    /\ tlaPlusSpec' = EmptyTLASpec
    /\ translationPhase' = "initial"
    /\ processedStatements' = <<>>
    /\ localVarSubscripts' = [v \in {} |-> <<>>]
    /\ fairnessOption' = NoFairness
    /\ errors' = <<>>

(* Load an AST for translation *)
LoadAST ==
    /\ translationPhase = "initial"
    /\ \E a \in [name: {"Algorithm"}, globalVariables: {<<>>}, processes: {<<>>}, definitions: {<<>>}, macros: {<<>>}]:
        /\ ast' = a
        /\ tlaPlusSpec' = [tlaPlusSpec EXCEPT !.moduleName = a.name]
        /\ translationPhase' = "explode_labels"
        /\ UNCHANGED <<processedStatements, localVarSubscripts, fairnessOption, errors>>

(* Phase 1: Explode labels *)
DoExplodeLabels ==
    /\ translationPhase = "explode_labels"
    /\ translationPhase' = "translate_calls_returns_gotos"
    /\ UNCHANGED <<ast, tlaPlusSpec, processedStatements, localVarSubscripts, fairnessOption, errors>>

(* Phase 2: Translate control flow *)
DoTranslateControlFlow ==
    /\ translationPhase = "translate_calls_returns_gotos"
    /\ translationPhase' = "add_var_subscripts"
    /\ UNCHANGED <<ast, tlaPlusSpec, processedStatements, localVarSubscripts, fairnessOption, errors>>

(* Phase 3: Add variable subscripts *)
DoAddVarSubscripts ==
    /\ translationPhase = "add_var_subscripts"
    /\ translationPhase' = "construct_init"
    /\ UNCHANGED <<ast, tlaPlusSpec, processedStatements, localVarSubscripts, fairnessOption, errors>>

(* Phase 4: Construct Init *)
DoConstructInit ==
    /\ translationPhase = "construct_init"
    /\ tlaPlusSpec' = [tlaPlusSpec EXCEPT !.init = ConstructInit(ast)]
    /\ translationPhase' = "construct_next"
    /\ UNCHANGED <<ast, processedStatements, localVarSubscripts, fairnessOption, errors>>

(* Phase 5: Construct Next *)
DoConstructNext ==
    /\ translationPhase = "construct_next"
    /\ tlaPlusSpec' = [tlaPlusSpec EXCEPT !.next = ConstructNext(ast, tlaPlusSpec.processActions)]
    /\ translationPhase' = "construct_spec"
    /\ UNCHANGED <<ast, processedStatements, localVarSubscripts, fairnessOption, errors>>

(* Phase 6: Construct Spec *)
DoConstructSpec ==
    /\ translationPhase = "construct_spec"
    /\ tlaPlusSpec' = [tlaPlusSpec EXCEPT 
        !.spec = ConstructSpec(tlaPlusSpec.init, tlaPlusSpec.next, fairnessOption)]
    /\ translationPhase' = "construct_termination"
    /\ UNCHANGED <<ast, processedStatements, localVarSubscripts, fairnessOption, errors>>

(* Phase 7: Construct Termination *)
DoConstructTermination ==
    /\ translationPhase = "construct_termination"
    /\ tlaPlusSpec' = [tlaPlusSpec EXCEPT !.termination = ConstructTermination]
    /\ translationPhase' = "complete"
    /\ UNCHANGED <<ast, processedStatements, localVarSubscripts, fairnessOption, errors>>

(* Set fairness option *)
SetFairnessOption ==
    /\ translationPhase = "initial"
    /\ \E f \in FairnessOptions:
        /\ fairnessOption' = f
        /\ UNCHANGED <<ast, tlaPlusSpec, translationPhase, processedStatements, localVarSubscripts, errors>>

(* Record an error *)
RecordError ==
    /\ \E errMsg \in STRING:
        /\ errors' = Append(errors, errMsg)
        /\ UNCHANGED <<ast, tlaPlusSpec, translationPhase, processedStatements, localVarSubscripts, fairnessOption>>

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ ast = EmptyAST
    /\ tlaPlusSpec = EmptyTLASpec
    /\ translationPhase = "initial"
    /\ processedStatements = <<>>
    /\ localVarSubscripts = [v \in {} |-> <<>>]
    /\ fairnessOption = NoFairness
    /\ errors = <<>>

-----------------------------------------------------------------------------
(* Next State Relation *)

Next ==
    \/ LoadAST
    \/ DoExplodeLabels
    \/ DoTranslateControlFlow
    \/ DoAddVarSubscripts
    \/ DoConstructInit
    \/ DoConstructNext
    \/ DoConstructSpec
    \/ DoConstructTermination
    \/ SetFairnessOption

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety Invariants *)

(* The translation phase is always valid *)
TypeInvariant ==
    /\ translationPhase \in TranslationPhases
    /\ fairnessOption \in FairnessOptions
    /\ ast.name \in Identifiers \cup {""}

(* Once complete, the spec has required components *)
CompletionInvariant ==
    translationPhase = "complete" =>
        /\ tlaPlusSpec.init # ""
        /\ tlaPlusSpec.next # ""
        /\ tlaPlusSpec.spec # ""
        /\ tlaPlusSpec.termination # ""

(* Fairness is only applied when constructing spec *)
FairnessInvariant ==
    (tlaPlusSpec.fairness # "") => 
        (fairnessOption # NoFairness)

(* Translation phases proceed in order *)
PhaseOrderInvariant ==
    /\ (translationPhase = "explode_labels") => (ast.name # "")
    /\ (translationPhase = "complete") => (tlaPlusSpec.moduleName # "")

-----------------------------------------------------------------------------
(* Liveness Properties *)

(* Translation eventually completes if started *)
TranslationEventuallyCompletes ==
    (ast.name # "") ~> (translationPhase = "complete")

(* If we start, we eventually have a valid spec *)
EventuallyValidSpec ==
    <>(translationPhase = "complete" /\ tlaPlusSpec.spec # "")

-----------------------------------------------------------------------------
(* Termination Property *)
Termination == <>(translationPhase = "complete")

=============================================================================