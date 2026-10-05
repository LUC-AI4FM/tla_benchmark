---------------------------- MODULE PlusCalTranslation ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    ProcNames,          \* Set of process names
    VarNames,           \* Set of variable names
    LabelNames,         \* Set of label names
    ExprValues,         \* Set of possible expression values
    MaxStmtDepth        \* Maximum depth for statement nesting

VARIABLES
    ast,                \* The abstract syntax tree being processed
    translationPhase,   \* Current phase of translation
    initPredicate,      \* The generated Init predicate
    nextAction,         \* The generated Next action
    specFormula,        \* The generated Spec formula
    fairnessOption,     \* Fairness option: "none", "wfProc", "wfNext", "sfProc"
    pcVar,              \* Program counter variable mapping
    processVars,        \* Process-local variables with subscripts
    labeledStmts,       \* Exploded labeled statements
    translationErrors   \* Any errors encountered during translation

vars == <<ast, translationPhase, initPredicate, nextAction, specFormula,
          fairnessOption, pcVar, processVars, labeledStmts, translationErrors>>

-----------------------------------------------------------------------------
(* AST Grammar Definitions as Sets and Predicates *)

(* A valid identifier is a non-empty string from VarNames or ProcNames or LabelNames *)
IsValidIdent(id) == id \in (VarNames \cup ProcNames \cup LabelNames)

(* Expression AST node *)
IsExpr(e) ==
    /\ e \in [type: {"literal", "var", "binop", "unop"}]
    /\ CASE e.type = "literal" -> e.value \in ExprValues
         [] e.type = "var" -> e.name \in VarNames
         [] e.type = "binop" -> /\ e.op \in {"+", "-", "*", "/", "=", "#", "<", ">", "<=", ">=", "/\\", "\\/"}
         [] e.type = "unop" -> e.op \in {"~", "-"}
         [] OTHER -> FALSE

(* Statement types in PlusCal *)
StmtTypes == {"assign", "if", "while", "call", "return", "goto", "skip", "print", "assert", "await", "with", "either"}

(* Variable declaration *)
IsVarDecl(v) ==
    /\ v \in [name: VarNames, initVal: ExprValues \cup {"undef"}]

(* Process definition *)
IsProcDef(p) ==
    /\ p \in [name: ProcNames, 
              vars: SUBSET [name: VarNames, initVal: ExprValues \cup {"undef"}],
              body: Seq([type: StmtTypes])]

(* Algorithm AST structure *)
IsAlgorithmAST(a) ==
    /\ a \in [name: STRING,
              globalVars: SUBSET [name: VarNames, initVal: ExprValues \cup {"undef"}],
              processes: SUBSET [name: ProcNames, vars: SUBSET [name: VarNames, initVal: ExprValues \cup {"undef"}]],
              fairness: {"none", "wfProc", "wfNext", "sfProc"}]

-----------------------------------------------------------------------------
(* Translation Phases *)

Phases == {"init", "explodeLabels", "translateCalls", "translateReturns", 
           "translateGotos", "addSubscripts", "constructInit", "constructNext",
           "constructSpec", "addFairness", "complete", "error"}

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ ast = [name |-> "EmptyAlgorithm",
              globalVars |-> {},
              processes |-> {},
              fairness |-> "none"]
    /\ translationPhase = "init"
    /\ initPredicate = [vars |-> {}, conjuncts |-> <<>>]
    /\ nextAction = [actions |-> {}, disjuncts |-> <<>>]
    /\ specFormula = [init |-> "", next |-> "", fairness |-> ""]
    /\ fairnessOption = "none"
    /\ pcVar = [proc |-> {}, initLabel |-> {}]
    /\ processVars = [proc |-> {}, localVars |-> {}]
    /\ labeledStmts = <<>>
    /\ translationErrors = <<>>

-----------------------------------------------------------------------------
(* Helper Operators for Translation *)

(* Add a subscript to a variable name for a process *)
AddSubscript(varName, procName) ==
    [name |-> varName, subscript |-> procName]

(* Check if a statement needs label explosion *)
NeedsExplosion(stmt) ==
    stmt.type \in {"if", "while", "either", "with"}

(* Generate program counter variable for a process *)
GenPCVar(procName) == 
    [var |-> "pc", proc |-> procName]

-----------------------------------------------------------------------------
(* Translation Actions *)

(* Load a new AST for translation *)
LoadAST ==
    /\ translationPhase = "init"
    /\ \E newAst \in [name: {"Algorithm"}, 
                      globalVars: SUBSET [name: VarNames, initVal: ExprValues \cup {"undef"}],
                      processes: SUBSET [name: ProcNames, vars: SUBSET [name: VarNames, initVal: ExprValues \cup {"undef"}]],
                      fairness: {"none", "wfProc", "wfNext", "sfProc"}]:
        /\ ast' = newAst
        /\ fairnessOption' = newAst.fairness
        /\ translationPhase' = "explodeLabels"
    /\ UNCHANGED <<initPredicate, nextAction, specFormula, pcVar, processVars, labeledStmts, translationErrors>>

(* Explode structured labeled statements into flat sequence *)
ExplodeLabels ==
    /\ translationPhase = "explodeLabels"
    /\ labeledStmts' = <<[label |-> "Start", stmts |-> <<>>]>>  \* Simplified explosion
    /\ translationPhase' = "translateCalls"
    /\ UNCHANGED <<ast, initPredicate, nextAction, specFormula, fairnessOption, pcVar, processVars, translationErrors>>

(* Translate call statements to appropriate TLA+ *)
TranslateCalls ==
    /\ translationPhase = "translateCalls"
    /\ translationPhase' = "translateReturns"
    /\ UNCHANGED <<ast, initPredicate, nextAction, specFormula, fairnessOption, pcVar, processVars, labeledStmts, translationErrors>>

(* Translate return statements *)
TranslateReturns ==
    /\ translationPhase = "translateReturns"
    /\ translationPhase' = "translateGotos"
    /\ UNCHANGED <<ast, initPredicate, nextAction, specFormula, fairnessOption, pcVar, processVars, labeledStmts, translationErrors>>

(* Translate goto statements to pc assignments *)
TranslateGotos ==
    /\ translationPhase = "translateGotos"
    /\ translationPhase' = "addSubscripts"
    /\ UNCHANGED <<ast, initPredicate, nextAction, specFormula, fairnessOption, pcVar, processVars, labeledStmts, translationErrors>>

(* Add subscripts to process-local variables *)
AddSubscriptsPhase ==
    /\ translationPhase = "addSubscripts"
    /\ processVars' = [proc |-> ast.processes, 
                       localVars |-> {AddSubscript(v.name, p.name) : 
                                      v \in p.vars, p \in ast.processes}]
    /\ translationPhase' = "constructInit"
    /\ UNCHANGED <<ast, initPredicate, nextAction, specFormula, fairnessOption, pcVar, labeledStmts, translationErrors>>

(* Construct Init predicate *)
ConstructInit ==
    /\ translationPhase = "constructInit"
    /\ initPredicate' = [vars |-> ast.globalVars \cup 
                                  UNION {p.vars : p \in ast.processes},
                         conjuncts |-> <<[type |-> "pcInit"]>>]
    /\ pcVar' = [proc |-> {p.name : p \in ast.processes},
                 initLabel |-> {[proc |-> p.name, label |-> "Start"] : p \in ast.processes}]
    /\ translationPhase' = "constructNext"
    /\ UNCHANGED <<ast, nextAction, specFormula, fairnessOption, processVars, labeledStmts, translationErrors>>

(* Construct Next action as disjunction of process actions *)
ConstructNext ==
    /\ translationPhase = "constructNext"
    /\ nextAction' = [actions |-> {[proc |-> p.name, action |-> "ProcAction"] : p \in ast.processes},
                      disjuncts |-> <<[type |-> "procDisjunct"]>>]
    /\ translationPhase' = "constructSpec"
    /\ UNCHANGED <<ast, initPredicate, specFormula, fairnessOption, pcVar, processVars, labeledStmts, translationErrors>>

(* Construct Spec formula with appropriate fairness *)
ConstructSpec ==
    /\ translationPhase = "constructSpec"
    /\ specFormula' = [init |-> "Init",
                       next |-> "[][Next]_vars",
                       fairness |-> CASE fairnessOption = "none" -> ""
                                      [] fairnessOption = "wfProc" -> "WF_vars(ProcActions)"
                                      [] fairnessOption = "wfNext" -> "WF_vars(Next)"
                                      [] fairnessOption = "sfProc" -> "SF_vars(ProcActions)"
                                      [] OTHER -> ""]
    /\ translationPhase' = "addFairness"
    /\ UNCHANGED <<ast, initPredicate, nextAction, fairnessOption, pcVar, processVars, labeledStmts, translationErrors>>

(* Add fairness conditions based on option *)
AddFairness ==
    /\ translationPhase = "addFairness"
    /\ translationPhase' = "complete"
    /\ UNCHANGED <<ast, initPredicate, nextAction, specFormula, fairnessOption, pcVar, processVars, labeledStmts, translationErrors>>

(* Handle translation errors *)
HandleError ==
    /\ translationPhase \in Phases \ {"complete", "error", "init"}
    /\ \E errMsg \in {"SyntaxError", "UndefinedVariable", "DuplicateLabel", "InvalidGoto"}:
        /\ translationErrors' = Append(translationErrors, errMsg)
        /\ translationPhase' = "error"
    /\ UNCHANGED <<ast, initPredicate, nextAction, specFormula, fairnessOption, pcVar, processVars, labeledStmts>>

(* Stutter when complete *)
Done ==
    /\ translationPhase \in {"complete", "error"}
    /\ UNCHANGED vars

-----------------------------------------------------------------------------
(* Next State Relation *)

Next ==
    \/ LoadAST
    \/ ExplodeLabels
    \/ TranslateCalls
    \/ TranslateReturns
    \/ TranslateGotos
    \/ AddSubscriptsPhase
    \/ ConstructInit
    \/ ConstructNext
    \/ ConstructSpec
    \/ AddFairness
    \/ HandleError
    \/ Done

-----------------------------------------------------------------------------
(* Specification with Fairness *)

(* Weak fairness on translation progress *)
Fairness == WF_vars(Next /\ translationPhase' # translationPhase)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety Invariants *)

(* Type invariant for the translation state *)
TypeInvariant ==
    /\ translationPhase \in Phases
    /\ fairnessOption \in {"none", "wfProc", "wfNext", "sfProc"}
    /\ labeledStmts \in Seq([label: LabelNames \cup {"Start", "Done"}, stmts: Seq([type: StmtTypes])])
    /\ translationErrors \in Seq({"SyntaxError", "UndefinedVariable", "DuplicateLabel", "InvalidGoto"})

(* No duplicate labels after explosion *)
NoDuplicateLabels ==
    LET labels == {labeledStmts[i].label : i \in DOMAIN labeledStmts}
    IN Cardinality(labels) = Len(labeledStmts)

(* Init and Next are defined when translation completes *)
TranslationComplete ==
    translationPhase = "complete" =>
        /\ initPredicate.vars # {}
        /\ nextAction.actions # {}

(* Fairness option preserved through translation *)
FairnessPreserved ==
    translationPhase = "complete" =>
        (fairnessOption = "none" => specFormula.fairness = "") /\
        (fairnessOption = "wfProc" => specFormula.fairness = "WF_vars(ProcActions)") /\
        (fairnessOption = "wfNext" => specFormula.fairness = "WF_vars(Next)") /\
        (fairnessOption = "sfProc" => specFormula.fairness = "SF_vars(ProcActions)")

(* All process variables have subscripts when translation completes *)
AllVarsSubscripted ==
    translationPhase = "complete" =>
        \A p \in ast.processes:
            \A v \in p.vars:
                \E sv \in processVars.localVars:
                    sv.name = v.name /\ sv.subscript = p.name

(* Safety: No errors means valid translation *)
SafeTranslation ==
    (translationPhase = "complete") => (translationErrors = <<>>)

-----------------------------------------------------------------------------
(* Liveness Properties *)

(* Translation eventually completes or errors *)
Termination == <>(translationPhase \in {"complete", "error"})

(* If no errors occur, translation completes *)
SuccessfulCompletion ==
    [](translationErrors = <<>> => <>(translationPhase = "complete"))

(* Each phase eventually transitions *)
PhaseProgress ==
    \A p \in Phases \ {"complete", "error", "init"}:
        [](translationPhase = p => <>(translationPhase # p))

=============================================================================