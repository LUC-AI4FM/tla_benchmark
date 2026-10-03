------------------------------ MODULE PlusCalASTTranslation ------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

(*
  This module sketches the translation from a PlusCal (global-naming) AST to TLA+.
  It defines:
   - An abstract grammar over records/sequences (predicates like IsStmt/IsProc/IsProgram).
   - A translation pipeline (ExplodeLabels, TranslateCallsReturns, ResolveGotos, AddSubscripts).
   - A final TLA+ behavior with Init, Next, Spec, and a Termination property.
   - Configurable fairness modeling: none, WF of process actions, WF of Next, SF of process actions.

  The state portion (pc, store) is intentionally minimal so the module is TLC-executable with a model
  that supplies finite Object and Any sets. The AST aspects are abstract and do not drive state here.
*)

CONSTANTS
  Any,      \* Universe of expression values used by the AST and variable store (model supplies a finite set).
  Object,   \* Universe of addresses/objects used as store keys (model supplies a finite set).
  Fairness  \* One of: "None", "WFProc", "WFNext", "SFProc".

(***************************************************************************)
(* Abstract syntax "grammar" as set/predicate characterizations            *)
(***************************************************************************)

TagSet == {
  "skip", "assign", "goto", "call", "return",
  "if", "either", "while", "with", "print",
  "label", "atomic", "nonatomic",
  "process", "procedure", "macro"
}

Maybe(S) == S \cup { "None" }

IsExpr(e) == e \in Any

IsStmt(s) ==
  /\ s \in [ op: TagSet,
             args: Seq(Any),
             label: Maybe(Any),
             target: Maybe(Any) ]
  /\ \A a \in s.args : IsExpr(a)

IsBlock(b) == b \in Seq(Any) /\ \A x \in DOMAIN b : IsStmt(b[x])

IsProc(p) ==
  /\ p \in [
       pid     : Any,
       locals  : SUBSET Any,
       body    : Seq(Any),
       start   : Maybe(Any),
       finals  : SUBSET Any
     ]
  /\ IsBlock(p.body)

IsProgram(ast) ==
  /\ ast \in [
       procs     : Seq(Any),
       globals   : SUBSET Any,
       body      : Seq(Any),
       options   : [ fairness : {"None","WFProc","WFNext","SFProc"} ],
       metadata  : [ source : Maybe(Any), notes : Maybe(Any) ]
     ]
  /\ \A i \in DOMAIN ast.procs : IsProc(ast.procs[i])
  /\ IsBlock(ast.body)

(***************************************************************************)
(* Translation pipeline operators (schematic stubs)                        *)
(***************************************************************************)

ExplodeLabels(ast) == ast

TranslateCallsReturns(ast) == ast

ResolveGotos(ast) == ast

AddSubscripts(ast) == ast

Normalize(ast) ==
  LET a1 == ExplodeLabels(ast) IN
  LET a2 == TranslateCallsReturns(a1) IN
  LET a3 == ResolveGotos(a2) IN
  AddSubscripts(a3)

\* Extracted semantic artifacts (placeholders returning this module's bindings)
BuildInitFrom(ast) == Init
BuildNextFrom(ast) == Next
BuildSpecFrom(ast) == Spec
BuildTerminationFrom(ast) == Termination

(***************************************************************************)
(* State and dynamics for the target TLA+ spec                             *)
(***************************************************************************)

VARIABLES pc, store

vars == << pc, store >>

\* In this abstract skeleton, the set of process ids and labels are empty.
\* This keeps the default dynamics stuttering-only unless a model overrides via additional operators.
ProcId == {}
Labels == {}

DefaultAny == CHOOSE v \in Any : TRUE
DefaultStore == [ o \in Object |-> DefaultAny ]

TypeOK ==
  /\ pc \in [ProcId -> Labels]
  /\ store \in [Object -> Any]

\* Process-local action template (here: no-op; never enabled; does not change state)
ProcAction(p) == FALSE /\ UNCHANGED vars

\* System-level step: a disjunction of per-process actions (none enabled here)
Step == \E p \in ProcId : ProcAction(p)

\* Next allows stuttering in the absence of enabled process actions
Next == Step \/ UNCHANGED vars

\* Initialization: well-typed state with default store; pc is the unique empty function
Init ==
  /\ TypeOK
  /\ pc = [ p \in ProcId |-> 0 ]
  /\ store = DefaultStore

(***************************************************************************)
(* Fairness modeling                                                       *)
(***************************************************************************)

FairnessModes == {"None","WFProc","WFNext","SFProc"}

WFConj ==
  CASE Fairness = "None"  -> TRUE
     [] Fairness = "WFProc" -> \A p \in ProcId : WF_vars(ProcAction(p))
     [] Fairness = "WFNext" -> WF_vars(Step)
     [] Fairness = "SFProc" -> \A p \in ProcId : SF_vars(ProcAction(p))
     [] OTHER               -> TRUE

Spec == Init /\ [][Next]_vars /\ WFConj

(***************************************************************************)
(* Termination property                                                    *)
(***************************************************************************)

\* Termination: eventually from some point on, no process action is enabled.
Termination == <>[] ( \A p \in ProcId : ~ENABLED ProcAction(p) )

=============================================================================