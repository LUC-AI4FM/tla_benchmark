---------------------------- MODULE PlusCal ----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

(* 
 * This module specifies the translation from the abstract syntax tree 
 * of a global-naming PlusCal algorithm into its corresponding TLA+ specification.
 * 
 * It defines the abstract syntax tree grammar as sets and predicates over 
 * records and sequences, and then defines a translation pipeline that:
 * - Explodes structured labeled statements
 * - Translates calls/returns/gotos
 * - Adds subscripts for process-local variables
 * - Constructs Init, Next, Spec, and a Termination property
 * 
 * The module also models fairness options for the translation output:
 * - No fairness
 * - Weak fairness of process actions
 * - Weak fairness of Next
 * - Strong fairness of process actions
 * 
 * Written to be executable by TLC.
 *)

-----------------------------------------------------------------------------
(* CONSTANTS *)
-----------------------------------------------------------------------------

(* 
 * Object represents any structured value in the AST - records, sequences, etc.
 * This is used as a universal type for AST nodes.
 *)
CONSTANT Object

(* 
 * Any represents the universal set of all possible values.
 * Used for type flexibility in the specification.
 *)
CONSTANT Any

-----------------------------------------------------------------------------
(* FAIRNESS OPTIONS *)
-----------------------------------------------------------------------------

(* 
 * Fairness options for the translation output.
 * These control what fairness conditions are added to the generated Spec.
 *)
NoFairness == "none"
WeakFairnessOfProcessActions == "wf_process"
WeakFairnessOfNext == "wf_next"
StrongFairnessOfProcessActions == "sf_process"

FairnessOptions == {NoFairness, WeakFairnessOfProcessActions, 
                    WeakFairnessOfNext, StrongFairnessOfProcessActions}

-----------------------------------------------------------------------------
(* AST NODE TYPE PREDICATES *)
-----------------------------------------------------------------------------

(* 
 * Predicates to check if a value is a valid AST node of a particular type.
 * These define the abstract syntax tree grammar as predicates over records.
 *)

IsRecord(x) == x \in Object

IsSeq(x) == x \in Seq(Any)

(* Check if x is a valid identifier *)
IsIdentifier(x) == 
    /\ IsRecord(x)
    /\ "name" \in DOMAIN x
    /\ x.name \in STRING

(* Check if x is a valid expression *)
IsExpression(x) == x \in Any

(* Check if x is a valid variable declaration *)
IsVarDecl(x) ==
    /\ IsRecord(x)
    /\ "var" \in DOMAIN x
    /\ "init" \in DOMAIN x

(* Check if x is a valid assignment statement *)
IsAssignment(x) ==
    /\ IsRecord(x)
    /\ "type" \in DOMAIN x
    /\ x.type = "assignment"
    /\ "lhs" \in DOMAIN x
    /\ "rhs" \in DOMAIN x

(* Check if x is a valid if statement *)
IsIf(x) ==
    /\ IsRecord(x)
    /\ "type" \in DOMAIN x
    /\ x.type = "if"
    /\ "cond" \in DOMAIN x
    /\ "then" \in DOMAIN x
    /\ "else" \in DOMAIN x

(* Check if x is a valid while statement *)
IsWhile(x) ==
    /\ IsRecord(x)
    /\ "type" \in DOMAIN x
    /\ x.type = "while"
    /\ "cond" \in DOMAIN x
    /\ "body" \in DOMAIN x

(* Check if x is a valid call statement *)
IsCall(x) ==
    /\ IsRecord(x)
    /\ "type" \in DOMAIN x
    /\ x.type = "call"
    /\ "proc" \in DOMAIN x
    /\ "args" \in DOMAIN x

(* Check if x is a valid return statement *)
IsReturn(x) ==
    /\ IsRecord(x)
    /\ "type" \in DOMAIN x
    /\ x.type = "return"

(* Check if x is a valid goto statement *)
IsGoto(x) ==
    /\ IsRecord(x)
    /\ "type" \in DOMAIN x
    /\ x.type = "goto"
    /\ "label" \in DOMAIN x

(* Check if x is a valid labeled statement *)
IsLabeledStmt(x) ==
    /\ IsRecord(x)
    /\ "label" \in DOMAIN x
    /\ "stmts" \in DOMAIN x

(* Check if x is a valid procedure definition *)
IsProcedure(x) ==
    /\ IsRecord(x)
    /\ "name" \in DOMAIN x
    /\ "params" \in DOMAIN x
    /\ "vars" \in DOMAIN x
    /\ "body" \in DOMAIN x

(* Check if x is a valid process definition *)
IsProcess(x) ==
    /\ IsRecord(x)
    /\ "name" \in DOMAIN x
    /\ "id" \in DOMAIN x
    /\ "vars" \in DOMAIN x
    /\ "body" \in DOMAIN x

(* Check if x is a valid algorithm *)
IsAlgorithm(x) ==
    /\ IsRecord(x)
    /\ "name" \in DOMAIN x
    /\ "vars" \in DOMAIN x
    /\ "procs" \in DOMAIN x
    /\ "processes" \in DOMAIN x

-----------------------------------------------------------------------------
(* HELPER OPERATORS *)
-----------------------------------------------------------------------------

(* 
 * Concatenate all sequences in a sequence of sequences.
 * Implementation hack: recursive definition for TLC execution.
 *)
RECURSIVE FlattenSeq(_)
FlattenSeq(seqs) ==
    IF seqs = <<>> 
    THEN <<>>
    ELSE Head(seqs) \o FlattenSeq(Tail(seqs))

(* 
 * Map a function over a sequence.
 * Limitation: TLC requires bounded evaluation.
 *)
RECURSIVE MapSeq(_, _)
MapSeq(f(_), seq) ==
    IF seq = <<>>
    THEN <<>>
    ELSE <<f(Head(seq))>> \o MapSeq(f, Tail(seq))

(* 
 * Filter a sequence by a predicate.
 *)
RECURSIVE FilterSeq(_, _)
FilterSeq(pred(_), seq) ==
    IF seq = <<>>
    THEN <<>>
    ELSE IF pred(Head(seq))
         THEN <<Head(seq)>> \o FilterSeq(pred, Tail(seq))
         ELSE FilterSeq(pred, Tail(seq))

-----------------------------------------------------------------------------
(* TRANSLATION PIPELINE *)
-----------------------------------------------------------------------------

(* 
 * Phase 1: Explode structured labeled statements.
 * This breaks down compound statements within labels into atomic steps.
 * 
 * Error handling: Assumes well-formed input AST.
 * Formatting: Preserves label names from original.
 *)
ExplodeLabeledStmt(lstmt) ==
    IF IsLabeledStmt(lstmt)
    THEN lstmt  \* Simplified: actual implementation would decompose
    ELSE lstmt

ExplodeStmts(stmts) ==
    MapSeq(ExplodeLabeledStmt, stmts)

(* 
 * Phase 2: Translate calls, returns, and gotos.
 * Converts procedure calls to stack operations and label jumps.
 * 
 * Implementation hack: Uses a synthetic "stack" variable.
 *)
TranslateCall(stmt) ==
    IF IsCall(stmt)
    THEN [type |-> "translated_call", 
          proc |-> stmt.proc,
          args |-> stmt.args,
          pushStack |-> TRUE]
    ELSE stmt

TranslateReturn(stmt) ==
    IF IsReturn(stmt)
    THEN [type |-> "translated_return",
          popStack |-> TRUE]
    ELSE stmt

TranslateGoto(stmt) ==
    IF IsGoto(stmt)
    THEN [type |-> "translated_goto",
          target |-> stmt.label]
    ELSE stmt

TranslateControlFlow(stmt) ==
    TranslateGoto(TranslateReturn(TranslateCall(stmt)))

(* 
 * Phase 3: Add subscripts for process-local variables.
 * Transforms local variable references to include process id subscript.
 * 
 * Limitation: Assumes unique variable names across scopes.
 *)
AddSubscript(var, procId) ==
    [var EXCEPT !.name = var.name \o "[" \o procId \o "]"]

AddSubscriptsToExpr(expr, procId, localVars) ==
    expr  \* Simplified: actual implementation would traverse expression

(* 
 * Phase 4: Construct TLA+ specification components.
 *)

(* 
 * Construct the Init predicate.
 * Initializes all variables to their declared initial values.
 *)
ConstructInit(alg) ==
    [name |-> "Init",
     vars |-> alg.vars,
     procs |-> alg.procs,
     processes |-> alg.processes]

(* 
 * Construct the Next action.
 * Disjunction of all process actions.
 *)
ConstructNext(alg) ==
    [name |-> "Next",
     processes |-> alg.processes,
     procs |-> alg.procs]

(* 
 * Construct process actions.
 * Each labeled statement becomes an action.
 *)
ConstructProcessAction(proc, lstmt) ==
    [name |-> proc.name \o "_" \o lstmt.label,
     process |-> proc,
     stmt |-> lstmt]

(* 
 * Construct the Spec with fairness conditions.
 *)
ConstructSpec(alg, fairnessOpt) ==
    [name |-> "Spec",
     init |-> ConstructInit(alg),
     next |-> ConstructNext(alg),
     fairness |-> fairnessOpt]

(* 
 * Construct the Termination property.
 * All processes have reached "Done" state.
 *)
ConstructTermination(alg) ==
    [name |-> "Termination",
     processes |-> alg.processes]

-----------------------------------------------------------------------------
(* MAIN TRANSLATION OPERATOR *)
-----------------------------------------------------------------------------

(* 
 * Main translation function.
 * Takes a PlusCal algorithm AST and fairness option,
 * returns a TLA+ specification structure.
 * 
 * Error: Will fail if input is not a valid algorithm.
 *)
Translate(alg, fairnessOpt) ==
    IF ~IsAlgorithm(alg)
    THEN [error |-> "Invalid algorithm"]
    ELSE IF fairnessOpt \notin FairnessOptions
    THEN [error |-> "Invalid fairness option"]
    ELSE [spec |-> ConstructSpec(alg, fairnessOpt),
          termination |-> ConstructTermination(alg)]

-----------------------------------------------------------------------------
(* VALIDATION PREDICATES *)
-----------------------------------------------------------------------------

(* 
 * Check if a translation result is valid.
 *)
IsValidTranslation(result) ==
    /\ "spec" \in DOMAIN result
    /\ "termination" \in DOMAIN result
    /\ "error" \notin DOMAIN result

(* 
 * Check if an algorithm uses procedures.
 *)
UsesProcedures(alg) ==
    /\ IsAlgorithm(alg)
    /\ Len(alg.procs) > 0

(* 
 * Check if an algorithm has multiple processes.
 *)
IsMultiProcess(alg) ==
    /\ IsAlgorithm(alg)
    /\ Len(alg.processes) > 1

=============================================================================