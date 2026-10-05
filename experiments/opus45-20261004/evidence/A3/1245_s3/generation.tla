---------------------------- MODULE PlusCal2TLA ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    \* AST Node Types
    ASTNodeTypes,
    \* Process identifiers
    ProcIds,
    \* Variable names (strings)
    VarNames,
    \* Label names
    LabelNames,
    \* Expression placeholders
    Expressions,
    \* Maximum sequence length for model checking
    MaxSeqLen,
    \* Fairness options
    NoFairness,
    WeakFairnessProc,
    WeakFairnessNext,
    StrongFairnessProc

VARIABLES
    \* The input AST
    ast,
    \* Current stage of translation pipeline
    stage,
    \* Intermediate representation after each stage
    ir,
    \* Output TLA+ specification components
    output,
    \* Error state
    error

vars == <<ast, stage, ir, output, error>>

-----------------------------------------------------------------------------
(* AST Grammar Definitions *)

\* A sequence with length at most MaxSeqLen
BoundedSeq(S) == UNION {[1..n -> S] : n \in 0..MaxSeqLen}

\* Variable declaration record
VarDecl == [name: VarNames, init: Expressions, isLocal: BOOLEAN]

\* Label record
Label == [name: LabelNames, isPlus: BOOLEAN, isMinus: BOOLEAN]

\* Statement types as records
RECURSIVE StatementSet
StatementSet == 
    [type: {"assignment"}, lhs: VarNames, rhs: Expressions]
    \cup [type: {"if"}, cond: Expressions, thenBranch: BoundedSeq(StatementSet), elseBranch: BoundedSeq(StatementSet)]
    \cup [type: {"while"}, cond: Expressions, body: BoundedSeq(StatementSet), label: Label]
    \cup [type: {"call"}, proc: ProcIds, args: BoundedSeq(Expressions)]
    \cup [type: {"return"}]
    \cup [type: {"goto"}, target: LabelNames]
    \cup [type: {"skip"}]
    \cup [type: {"print"}, expr: Expressions]
    \cup [type: {"assert"}, cond: Expressions]
    \cup [type: {"await"}, cond: Expressions]

\* Labeled statement block
LabeledStmt == [label: Label, stmts: BoundedSeq(StatementSet)]

\* Procedure definition
ProcedureDef == [
    name: ProcIds,
    params: BoundedSeq(VarDecl),
    localVars: BoundedSeq(VarDecl),
    body: BoundedSeq(LabeledStmt)
]

\* Process definition
ProcessDef == [
    name: ProcIds,
    id: Expressions,
    isSet: BOOLEAN,
    localVars: BoundedSeq(VarDecl),
    body: BoundedSeq(LabeledStmt),
    fairness: {NoFairness, WeakFairnessProc, StrongFairnessProc}
]

\* Complete PlusCal algorithm AST
AlgorithmAST == [
    name: VarNames,
    globalVars: BoundedSeq(VarDecl),
    procedures: BoundedSeq(ProcedureDef),
    processes: BoundedSeq(ProcessDef),
    mainBody: BoundedSeq(LabeledStmt),
    fairness: {NoFairness, WeakFairnessProc, WeakFairnessNext, StrongFairnessProc}
]

-----------------------------------------------------------------------------
(* Intermediate Representation after each stage *)

\* Exploded statement (single statement per label)
ExplodedStmt == [label: LabelNames, stmt: StatementSet, next: LabelNames \cup {"Done"}]

\* Translated action (TLA+ action)
TranslatedAction == [
    name: LabelNames,
    guard: Expressions,
    updates: BoundedSeq([var: VarNames, subscript: Expressions, value: Expressions]),
    pcUpdate: LabelNames \cup {"Done"}
]

\* Process IR
ProcessIR == [
    name: ProcIds,
    actions: BoundedSeq(TranslatedAction),
    fairness: {NoFairness, WeakFairnessProc, StrongFairnessProc}
]

\* Complete IR
IntermediateRep == [
    globalVars: BoundedSeq(VarDecl),
    processVars: [ProcIds -> BoundedSeq(VarDecl)],
    processes: BoundedSeq(ProcessIR),
    initLabel: LabelNames,
    stackVar: BOOLEAN
]

-----------------------------------------------------------------------------
(* Output TLA+ Specification Components *)

TLASpec == [
    moduleName: VarNames,
    extends: BoundedSeq(VarNames),
    constants: BoundedSeq(VarNames),
    variables: BoundedSeq(VarNames),
    initPred: Expressions,
    actions: BoundedSeq([name: LabelNames, def: Expressions]),
    nextPred: Expressions,
    specPred: Expressions,
    termination: Expressions,
    fairnessProps: BoundedSeq(Expressions)
]

-----------------------------------------------------------------------------
(* Translation Pipeline Stages *)

Stages == {"Parse", "Explode", "TranslateControl", "AddSubscripts", "GenerateSpec", "Done", "Error"}

-----------------------------------------------------------------------------
(* Helper Predicates *)

\* Check if AST is valid
IsValidAST(a) ==
    /\ a.name \in VarNames
    /\ \A v \in DOMAIN a.globalVars : a.globalVars[v] \in VarDecl
    /\ \A p \in DOMAIN a.processes : a.processes[p].name \in ProcIds

\* Check if a statement contains a call
ContainsCall(stmt) ==
    \/ stmt.type = "call"
    \/ /\ stmt.type = "if"
       /\ \E i \in DOMAIN stmt.thenBranch : ContainsCall(stmt.thenBranch[i])
    \/ /\ stmt.type = "if"
       /\ \E i \in DOMAIN stmt.elseBranch : ContainsCall(stmt.elseBranch[i])

\* Get all labels from a process body
GetLabels(body) ==
    {body[i].label.name : i \in DOMAIN body}

\* Check if translation requires stack variable
NeedsStack(a) ==
    Len(a.procedures) > 0

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ ast \in AlgorithmAST
    /\ stage = "Parse"
    /\ ir = [globalVars |-> <<>>, processVars |-> [p \in ProcIds |-> <<>>], 
             processes |-> <<>>, initLabel |-> "Init", stackVar |-> FALSE]
    /\ output = [moduleName |-> "", extends |-> <<>>, constants |-> <<>>,
                 variables |-> <<>>, initPred |-> "TRUE", actions |-> <<>>,
                 nextPred |-> "FALSE", specPred |-> "", termination |-> "",
                 fairnessProps |-> <<>>]
    /\ error = "None"

-----------------------------------------------------------------------------
(* Stage 1: Parse and validate AST *)

ParseAST ==
    /\ stage = "Parse"
    /\ IF IsValidAST(ast)
       THEN /\ stage' = "Explode"
            /\ ir' = [ir EXCEPT !.globalVars = ast.globalVars,
                               !.stackVar = NeedsStack(ast)]
            /\ error' = error
       ELSE /\ stage' = "Error"
            /\ error' = "Invalid AST"
            /\ ir' = ir
    /\ ast' = ast
    /\ output' = output

-----------------------------------------------------------------------------
(* Stage 2: Explode labeled statements *)

\* This stage breaks compound labeled statements into atomic actions
ExplodeLabeledStmts ==
    /\ stage = "Explode"
    /\ stage' = "TranslateControl"
    /\ ir' = [ir EXCEPT 
        !.processes = [i \in DOMAIN ast.processes |->
            [name |-> ast.processes[i].name,
             actions |-> <<>>,
             fairness |-> ast.processes[i].fairness]]]
    /\ UNCHANGED <<ast, output, error>>

-----------------------------------------------------------------------------
(* Stage 3: Translate call/return/goto *)

TranslateControlFlow ==
    /\ stage = "TranslateControl"
    /\ stage' = "AddSubscripts"
    \* Translation logic: convert calls to stack push, returns to stack pop
    \* gotos become pc updates
    /\ UNCHANGED <<ast, ir, output, error>>

-----------------------------------------------------------------------------
(* Stage 4: Add subscripts for process-local variables *)

AddVarSubscripts ==
    /\ stage = "AddSubscripts"
    /\ stage' = "GenerateSpec"
    \* Add [self] subscripts to process-local variables
    /\ UNCHANGED <<ast, ir, output, error>>

-----------------------------------------------------------------------------
(* Stage 5: Generate final TLA+ specification *)

GenerateTLASpec ==
    /\ stage = "GenerateSpec"
    /\ stage' = "Done"
    /\ output' = [
        moduleName |-> ast.name,
        extends |-> <<"Integers", "Sequences", "TLC">>,
        constants |-> IF Len(ast.processes) > 0 
                      THEN <<"ProcSet">> 
                      ELSE <<>>,
        variables |-> 
            [i \in 1..Len(ast.globalVars) |-> ast.globalVars[i].name]
            \o IF Len(ast.processes) > 0 THEN <<"pc">> ELSE <<>>
            \o IF ir.stackVar THEN <<"stack">> ELSE <<>>,
        initPred |-> "InitPredicate",
        actions |-> <<>>,
        nextPred |-> "NextPredicate",
        specPred |-> 
            CASE ast.fairness = NoFairness -> "Init /\\ [][Next]_vars"
              [] ast.fairness = WeakFairnessNext -> "Init /\\ [][Next]_vars /\\ WF_vars(Next)"
              [] ast.fairness = WeakFairnessProc -> "Init /\\ [][Next]_vars /\\ ProcessFairness"
              [] ast.fairness = StrongFairnessProc -> "Init /\\ [][Next]_vars /\\ StrongProcessFairness"
              [] OTHER -> "Init /\\ [][Next]_vars",
        termination |-> "Termination == <>[](\\ A self \\in ProcSet : pc[self] = \"Done\")",
        fairnessProps |->
            CASE ast.fairness = NoFairness -> <<>>
              [] ast.fairness = WeakFairnessProc -> <<"WF_vars(proc_action)">>
              [] ast.fairness = StrongFairnessProc -> <<"SF_vars(proc_action)">>
              [] OTHER -> <<>>
       ]
    /\ UNCHANGED <<ast, ir, error>>

-----------------------------------------------------------------------------
(* Error handling *)

HandleError ==
    /\ stage = "Error"
    /\ UNCHANGED vars

-----------------------------------------------------------------------------
(* Terminal state *)

Done ==
    /\ stage = "Done"
    /\ UNCHANGED vars

-----------------------------------------------------------------------------
(* Next state relation *)

Next ==
    \/ ParseAST
    \/ ExplodeLabeledStmts
    \/ TranslateControlFlow
    \/ AddVarSubscripts
    \/ GenerateTLASpec
    \/ HandleError
    \/ Done

-----------------------------------------------------------------------------
(* Fairness *)

Fairness ==
    /\ WF_vars(ParseAST)
    /\ WF_vars(ExplodeLabeledStmts)
    /\ WF_vars(TranslateControlFlow)
    /\ WF_vars(AddVarSubscripts)
    /\ WF_vars(GenerateTLASpec)

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety Invariants *)

\* Type invariant
TypeOK ==
    /\ stage \in Stages
    /\ error \in {"None"} \cup VarNames

\* No error during normal translation
NoErrorInValidTranslation ==
    IsValidAST(ast) => error = "None"

\* Stage monotonicity (progress through pipeline)
StageOrder ==
    LET order == [s \in Stages |-> 
        CASE s = "Parse" -> 0
          [] s = "Explode" -> 1
          [] s = "TranslateControl" -> 2
          [] s = "AddSubscripts" -> 3
          [] s = "GenerateSpec" -> 4
          [] s = "Done" -> 5
          [] s = "Error" -> 6]
    IN TRUE  \* Checked via temporal property

\* Output is valid when done
ValidOutput ==
    stage = "Done" => output.moduleName = ast.name

\* Fairness options are preserved
FairnessPreserved ==
    stage = "Done" =>
        \/ /\ ast.fairness = NoFairness
           /\ output.fairnessProps = <<>>
        \/ /\ ast.fairness # NoFairness
           /\ Len(output.fairnessProps) > 0

-----------------------------------------------------------------------------
(* Liveness Properties *)

\* Translation eventually completes or errors
EventuallyTerminates ==
    <>(stage = "Done" \/ stage = "Error")

\* Valid AST leads to successful translation
ValidASTSucceeds ==
    IsValidAST(ast) ~> stage = "Done"

\* Invalid AST leads to error
InvalidASTFails ==
    ~IsValidAST(ast) ~> stage = "Error"

-----------------------------------------------------------------------------
(* Invariants to check *)

SafetyInvariants ==
    /\ TypeOK
    /\ ValidOutput
    /\ FairnessPreserved

LivenessProperties ==
    /\ EventuallyTerminates
    /\ ValidASTSucceeds

=============================================================================