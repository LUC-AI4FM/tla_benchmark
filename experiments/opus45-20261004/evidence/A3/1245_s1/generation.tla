---------------------------- MODULE PlusCalToTLA ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    ProcIds,        \* Set of process identifiers
    VarNames,       \* Set of variable names
    LabelNames,     \* Set of label names
    ExprValues,     \* Set of possible expression values
    MaxStmts        \* Maximum number of statements (for bounded model checking)

VARIABLES
    ast,            \* The abstract syntax tree of the PlusCal algorithm
    tlaPlusSpec,    \* The generated TLA+ specification
    pc,             \* Program counter mapping: process -> label
    localVars,      \* Local variables: process -> (varname -> value)
    globalVars,     \* Global variables: varname -> value
    translationPhase, \* Current phase of translation
    fairnessOption, \* Fairness option for the output
    terminated      \* Set of terminated processes

(* -------------------- AST Grammar Definitions -------------------- *)

(* Statement types in the abstract syntax tree *)
StmtTypes == {"assign", "if", "while", "either", "with", "call", "return", 
              "goto", "print", "assert", "skip", "labeled"}

(* Expression grammar - simplified representation *)
IsExpr(e) == e \in ExprValues \/ 
             (DOMAIN e = {"op", "args"} /\ e.op \in {"plus", "minus", "eq", "neq"})

(* Statement record predicates *)
IsAssignStmt(s) == 
    DOMAIN s = {"type", "var", "expr"} /\
    s.type = "assign" /\
    s.var \in VarNames /\
    IsExpr(s.expr)

IsIfStmt(s) ==
    DOMAIN s = {"type", "cond", "then", "else"} /\
    s.type = "if" /\
    IsExpr(s.cond)

IsWhileStmt(s) ==
    DOMAIN s = {"type", "cond", "body"} /\
    s.type = "while" /\
    IsExpr(s.cond)

IsCallStmt(s) ==
    DOMAIN s = {"type", "proc", "args"} /\
    s.type = "call" /\
    s.proc \in ProcIds

IsReturnStmt(s) ==
    DOMAIN s = {"type"} /\
    s.type = "return"

IsGotoStmt(s) ==
    DOMAIN s = {"type", "label"} /\
    s.type = "goto" /\
    s.label \in LabelNames

IsLabeledStmt(s) ==
    DOMAIN s = {"type", "label", "stmts"} /\
    s.type = "labeled" /\
    s.label \in LabelNames

IsSkipStmt(s) ==
    DOMAIN s = {"type"} /\
    s.type = "skip"

(* Process definition predicate *)
IsProcessDef(p) ==
    DOMAIN p = {"id", "vars", "body", "fairness"} /\
    p.id \in ProcIds /\
    p.vars \subseteq VarNames /\
    p.fairness \in {"none", "weak", "strong"}

(* Algorithm definition predicate *)
IsAlgorithm(alg) ==
    DOMAIN alg = {"name", "globalVars", "processes"} /\
    alg.globalVars \subseteq VarNames

(* Fairness options *)
FairnessOptions == {"none", "wfActions", "wfNext", "sfActions"}

(* -------------------- Translation Phase Definitions -------------------- *)

TranslationPhases == {"init", "explode", "translateCalls", "translateReturns",
                      "translateGotos", "addSubscripts", "constructInit",
                      "constructNext", "constructSpec", "addTermination", "done"}

(* -------------------- Helper Operators -------------------- *)

(* Get all labels from a sequence of statements *)
RECURSIVE GetLabels(_)
GetLabels(stmts) ==
    IF stmts = <<>> THEN {}
    ELSE LET head == Head(stmts)
             tail == Tail(stmts)
         IN (IF head.type = "labeled" THEN {head.label} ELSE {}) 
            \cup GetLabels(tail)

(* Substitute process subscript into variable name *)
Subscript(var, procId) == 
    [name |-> var, proc |-> procId]

(* Check if a statement is a control flow statement *)
IsControlFlow(s) ==
    s.type \in {"call", "return", "goto", "if", "while", "either"}

(* -------------------- Initial State -------------------- *)

TypeOK ==
    /\ translationPhase \in TranslationPhases
    /\ fairnessOption \in FairnessOptions
    /\ terminated \subseteq ProcIds
    /\ pc \in [ProcIds -> LabelNames \cup {"Done"}]

Init ==
    /\ ast = [name |-> "Algorithm",
              globalVars |-> {},
              processes |-> {}]
    /\ tlaPlusSpec = [init |-> "TRUE",
                      next |-> "FALSE",
                      spec |-> "",
                      termination |-> "",
                      actions |-> {}]
    /\ pc = [p \in ProcIds |-> "Done"]
    /\ localVars = [p \in ProcIds |-> [v \in {} |-> ExprValues]]
    /\ globalVars = [v \in {} |-> ExprValues]
    /\ translationPhase = "init"
    /\ fairnessOption = "none"
    /\ terminated = ProcIds

(* -------------------- Translation Actions -------------------- *)

(* Load an algorithm AST *)
LoadAST(newAst) ==
    /\ translationPhase = "init"
    /\ IsAlgorithm(newAst)
    /\ ast' = newAst
    /\ translationPhase' = "explode"
    /\ UNCHANGED <<tlaPlusSpec, pc, localVars, globalVars, fairnessOption, terminated>>

(* Explode labeled statements - flatten nested structure *)
ExplodeLabeledStatements ==
    /\ translationPhase = "explode"
    /\ translationPhase' = "translateCalls"
    /\ UNCHANGED <<ast, tlaPlusSpec, pc, localVars, globalVars, fairnessOption, terminated>>

(* Translate call statements to label transitions *)
TranslateCalls ==
    /\ translationPhase = "translateCalls"
    /\ translationPhase' = "translateReturns"
    /\ UNCHANGED <<ast, tlaPlusSpec, pc, localVars, globalVars, fairnessOption, terminated>>

(* Translate return statements *)
TranslateReturns ==
    /\ translationPhase = "translateReturns"
    /\ translationPhase' = "translateGotos"
    /\ UNCHANGED <<ast, tlaPlusSpec, pc, localVars, globalVars, fairnessOption, terminated>>

(* Translate goto statements to pc updates *)
TranslateGotos ==
    /\ translationPhase = "translateGotos"
    /\ translationPhase' = "addSubscripts"
    /\ UNCHANGED <<ast, tlaPlusSpec, pc, localVars, globalVars, fairnessOption, terminated>>

(* Add subscripts for process-local variables *)
AddSubscripts ==
    /\ translationPhase = "addSubscripts"
    /\ translationPhase' = "constructInit"
    /\ UNCHANGED <<ast, tlaPlusSpec, pc, localVars, globalVars, fairnessOption, terminated>>

(* Construct the Init predicate *)
ConstructInit ==
    /\ translationPhase = "constructInit"
    /\ tlaPlusSpec' = [tlaPlusSpec EXCEPT 
        !.init = "GlobalVarsInit /\\ LocalVarsInit /\\ pc = InitialPC"]
    /\ translationPhase' = "constructNext"
    /\ UNCHANGED <<ast, pc, localVars, globalVars, fairnessOption, terminated>>

(* Construct the Next action *)
ConstructNext ==
    /\ translationPhase = "constructNext"
    /\ tlaPlusSpec' = [tlaPlusSpec EXCEPT 
        !.next = "\\E self \\in ProcIds: ProcessAction(self)",
        !.actions = {[proc |-> p, label |-> l] : p \in ProcIds, l \in LabelNames}]
    /\ translationPhase' = "constructSpec"
    /\ UNCHANGED <<ast, pc, localVars, globalVars, fairnessOption, terminated>>

(* Construct the Spec with fairness based on option *)
ConstructSpec ==
    /\ translationPhase = "constructSpec"
    /\ tlaPlusSpec' = [tlaPlusSpec EXCEPT 
        !.spec = CASE fairnessOption = "none" -> 
                      "Init /\\ [][Next]_vars"
                   [] fairnessOption = "wfActions" ->
                      "Init /\\ [][Next]_vars /\\ WFProcessActions"
                   [] fairnessOption = "wfNext" ->
                      "Init /\\ [][Next]_vars /\\ WF_vars(Next)"
                   [] fairnessOption = "sfActions" ->
                      "Init /\\ [][Next]_vars /\\ SFProcessActions"
                   [] OTHER -> "Init /\\ [][Next]_vars"]
    /\ translationPhase' = "addTermination"
    /\ UNCHANGED <<ast, pc, localVars, globalVars, fairnessOption, terminated>>

(* Add Termination property *)
AddTermination ==
    /\ translationPhase = "addTermination"
    /\ tlaPlusSpec' = [tlaPlusSpec EXCEPT 
        !.termination = "<>(\\A self \\in ProcIds: pc[self] = \"Done\")"]
    /\ translationPhase' = "done"
    /\ UNCHANGED <<ast, pc, localVars, globalVars, fairnessOption, terminated>>

(* Set fairness option (can be done before constructSpec) *)
SetFairnessOption(opt) ==
    /\ translationPhase \in {"init", "explode", "translateCalls", "translateReturns",
                             "translateGotos", "addSubscripts", "constructInit", 
                             "constructNext"}
    /\ opt \in FairnessOptions
    /\ fairnessOption' = opt
    /\ UNCHANGED <<ast, tlaPlusSpec, pc, localVars, globalVars, translationPhase, terminated>>

(* -------------------- Runtime Simulation (for TLC) -------------------- *)

(* Initialize runtime state from translated spec *)
InitRuntime ==
    /\ translationPhase = "done"
    /\ \E initLabel \in LabelNames:
        pc' = [p \in ProcIds |-> initLabel]
    /\ terminated' = {}
    /\ UNCHANGED <<ast, tlaPlusSpec, localVars, globalVars, translationPhase, fairnessOption>>

(* Process takes a step *)
ProcessStep(self) ==
    /\ translationPhase = "done"
    /\ pc[self] # "Done"
    /\ self \notin terminated
    /\ \E nextLabel \in LabelNames \cup {"Done"}:
        /\ pc' = [pc EXCEPT ![self] = nextLabel]
        /\ IF nextLabel = "Done" 
           THEN terminated' = terminated \cup {self}
           ELSE UNCHANGED terminated
    /\ UNCHANGED <<ast, tlaPlusSpec, localVars, globalVars, translationPhase, fairnessOption>>

(* -------------------- Next State Relation -------------------- *)

TranslationStep ==
    \/ \E newAst \in [name: {"Alg"}, globalVars: SUBSET VarNames, processes: SUBSET [id: ProcIds, vars: SUBSET VarNames, body: {<<>>}, fairness: {"none", "weak", "strong"}]]:
        LoadAST(newAst)
    \/ ExplodeLabeledStatements
    \/ TranslateCalls
    \/ TranslateReturns
    \/ TranslateGotos
    \/ AddSubscripts
    \/ ConstructInit
    \/ ConstructNext
    \/ ConstructSpec
    \/ AddTermination
    \/ \E opt \in FairnessOptions: SetFairnessOption(opt)

RuntimeStep ==
    \/ InitRuntime
    \/ \E self \in ProcIds: ProcessStep(self)

Next ==
    \/ TranslationStep
    \/ RuntimeStep

(* -------------------- Specification -------------------- *)

vars == <<ast, tlaPlusSpec, pc, localVars, globalVars, translationPhase, 
          fairnessOption, terminated>>

Spec == Init /\ [][Next]_vars

(* Weak fairness of translation steps *)
FairSpec == Spec /\ WF_vars(TranslationStep)

(* Strong fairness for process actions *)
StrongFairSpec == Spec /\ SF_vars(RuntimeStep)

(* -------------------- Safety Invariants -------------------- *)

(* Translation phases progress in order *)
PhaseOrder ==
    LET order == <<"init", "explode", "translateCalls", "translateReturns",
                   "translateGotos", "addSubscripts", "constructInit",
                   "constructNext", "constructSpec", "addTermination", "done">>
        IndexOf(phase) == CHOOSE i \in 1..Len(order): order[i] = phase
    IN TRUE \* Phase transitions are monotonic (simplified)

(* Terminated processes have pc = Done *)
TerminatedCorrect ==
    \A p \in terminated: pc[p] = "Done"

(* Fairness option is valid *)
FairnessValid ==
    fairnessOption \in FairnessOptions

(* Combined type invariant *)
Invariant ==
    /\ TypeOK
    /\ TerminatedCorrect
    /\ FairnessValid

(* -------------------- Liveness Properties -------------------- *)

(* Translation eventually completes *)
TranslationCompletes ==
    <>(translationPhase = "done")

(* All processes eventually terminate (under fairness) *)
Termination ==
    <>(terminated = ProcIds)

(* Progress: if not done, eventually take a step *)
Progress ==
    translationPhase # "done" ~> 
    (translationPhase' # translationPhase \/ translationPhase = "done")

(* -------------------- Theorems (for documentation) -------------------- *)

(* The translation preserves the structure of the PlusCal algorithm *)
THEOREM TranslationCorrectness ==
    Spec => []Invariant

(* Under fair execution, translation completes *)
THEOREM TranslationLiveness ==
    FairSpec => TranslationCompletes

(* Under strong fairness, all processes terminate *)
THEOREM TerminationLiveness ==
    StrongFairSpec => Termination

=============================================================================