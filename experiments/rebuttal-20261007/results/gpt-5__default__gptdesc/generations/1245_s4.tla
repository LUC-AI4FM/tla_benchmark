----------------------------- MODULE PlusCalTranslation -----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*
  This module specifies, at a meta level, a translation pipeline from a global-naming
  PlusCal abstract syntax tree (AST) to a corresponding TLA+ specification.
  The AST, intermediate forms, and the produced artifact are modeled as records and
  sequences. The pipeline has four transforming stages:
    1) explode structured labeled statements,
    2) translate calls/returns/gotos,
    3) add subscripts for process-local variables,
    4) build the Init/Next/Spec product.
  The module is executable by TLC (given finite constants) and includes safety
  invariants, a termination property, and fairness options that model the fairness
  choices offered for the translation output: none, weak fairness of process actions,
  weak fairness of Next, and strong fairness of process actions.
*)

CONSTANTS
  AST,       \* Input abstract syntax tree (opaque to this spec except shape predicates)
  PROCS,     \* Set of process identifiers (finite for TLC execution)
  FAIRNESS   \* One of {"None","WFProc","WFNext","SFProc"} controlling fairness mode

(***************************************************************************)
(* Syntax and typing domains                                               *)
(***************************************************************************)

STAGES == {"explode","calls","subscripts","build","done"}

FAIRNESSOPS == {"None","WFProc","WFNext","SFProc"}

ASSUME FAIRNESS \in FAIRNESSOPS

(*
  Minimal statement tags used across pipeline stages. This is intentionally
  coarse: the "explode" stage yields only BASIC1 forms; the "calls" stage
  yields only BASIC2 forms (i.e., after rewriting call/return/goto).
*)
BASIC1 == {"Assign","Goto","Call","Return","Skip"}
BASIC2 == {"Assign","Jump","CallRet","Skip"}

LStmt1Type == [label: Nat, kind: BASIC1, arg: Nat]
LStmt2Type == [label: Nat, kind: BASIC2, arg: Nat]

(***************************************************************************)
(* Translation predicates (contracts of each pipeline stage)               *)
(***************************************************************************)

ExplodeOK(ast, e) ==
  /\ e \in Seq(LStmt1Type)
  \* Intuition: 'e' is a flat sequence of labeled basic statements; all structured
  \* statements in 'ast' have been "exploded" away.

TranslateCallsOK(e, r) ==
  /\ e \in Seq(LStmt1Type)
  /\ r \in Seq(LStmt2Type)
  \* Intuition: calls/returns/gotos are transformed into basic control-flow arities.

AddSubscriptsOK(r, s) ==
  /\ r \in Seq(LStmt2Type)
  /\ s \in [ stmts: Seq(LStmt2Type), locals: [PROCS -> SUBSET Nat] ]
  \* Intuition: locals[p] is the set of variable identifiers that have been
  \* subscriped by process 'p'; stmts remain in BASIC2 normal form.

BuildSpecOK(s, p) ==
  /\ s \in [ stmts: Seq(LStmt2Type), locals: [PROCS -> SUBSET Nat] ]
  /\ p \in [ Vars: SUBSET Nat,
             Init: Nat,
             Next: Nat,
             Termination: Nat,
             fairness: FAIRNESSOPS ]
  \* Intuition: Vars is the set of (symbolic) variables in the produced spec;
  \* Init/Next/Termination are abstract codes here (Nat-encoded);
  \* fairness encodes the chosen fairness mode.

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)

VARIABLES
  ast,           \* immutable copy of AST input
  stage,         \* current pipeline stage
  exploded,      \* result of Explode
  routed,        \* result after translating calls/returns/gotos
  subscripted,   \* result after adding process-local subscripts
  product,       \* built product containing Vars/Init/Next/Termination/fairness
  errs,          \* set of error codes (Nats) accumulated (left abstract)
  pc             \* per-process post-build bookkeeping for fairness modeling

vars == << ast, stage, exploded, routed, subscripted, product, errs, pc >>

(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)

Init ==
  /\ ast = AST
  /\ stage = "explode"
  /\ exploded = << >>
  /\ routed = << >>
  /\ subscripted = [ stmts |-> << >>, locals |-> [p \in PROCS |-> {}] ]
  /\ product = [ Vars |-> {}, Init |-> 0, Next |-> 0, Termination |-> 0, fairness |-> FAIRNESS ]
  /\ errs = {}
  /\ pc = [ p \in PROCS |-> "ready" ]

(***************************************************************************)
(* Actions for each pipeline stage                                         *)
(***************************************************************************)

DoExplode ==
  /\ stage = "explode"
  /\ \E e \in Seq(LStmt1Type): ExplodeOK(ast, e) /\ exploded' = e
  /\ stage' = "calls"
  /\ UNCHANGED << ast, routed, subscripted, product, errs, pc >>

DoCalls ==
  /\ stage = "calls"
  /\ ExplodeOK(ast, exploded)
  /\ \E r \in Seq(LStmt2Type): TranslateCallsOK(exploded, r) /\ routed' = r
  /\ stage' = "subscripts"
  /\ UNCHANGED << ast, exploded, subscripted, product, errs, pc >>

DoSubscripts ==
  /\ stage = "subscripts"
  /\ TranslateCallsOK(exploded, routed)
  /\ \E s \in [ stmts: Seq(LStmt2Type), locals: [PROCS -> SUBSET Nat] ]:
        AddSubscriptsOK(routed, s) /\ subscripted' = s
  /\ stage' = "build"
  /\ UNCHANGED << ast, exploded, routed, product, errs, pc >>

DoBuild ==
  /\ stage = "build"
  /\ AddSubscriptsOK(routed, subscripted)
  /\ \E p \in [ Vars: SUBSET Nat,
                Init: Nat, Next: Nat, Termination: Nat, fairness: FAIRNESSOPS ]:
        BuildSpecOK(subscripted, p) /\ product' = [p EXCEPT !.fairness = FAIRNESS]
  /\ stage' = "done"
  /\ UNCHANGED << ast, exploded, routed, subscripted, errs, pc >>

(*
  Process-level action used only to instantiate the "fairness of process actions"
  modes. It is enabled after the build is done and marks each process as done.
*)
ProcAction(p) ==
  /\ p \in PROCS
  /\ stage = "done"
  /\ pc[p] = "ready"
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << ast, stage, exploded, routed, subscripted, product, errs >>

ProcActAny == \E p \in PROCS: ProcAction(p)

(*
  Stuttering is always allowed; the fairness modes below can be used to constrain
  execution if desired.
*)
Stutter == UNCHANGED vars

Next == DoExplode \/ DoCalls \/ DoSubscripts \/ DoBuild \/ ProcActAny \/ Stutter

(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)

AstConstInv ==
  ast = AST

StageTypeInv ==
  stage \in STAGES

ErrsTypeInv ==
  errs \subseteq Nat

ExplodedTypeInv ==
  (stage \in {"calls","subscripts","build","done"}) =>
    exploded \in Seq(LStmt1Type)

RoutedTypeInv ==
  (stage \in {"subscripts","build","done"}) =>
    routed \in Seq(LStmt2Type)

SubscriptedTypeInv ==
  (stage \in {"build","done"}) =>
    subscripted \in [ stmts: Seq(LStmt2Type), locals: [PROCS -> SUBSET Nat] ]

ProductTypeInv ==
  (stage = "done") =>
    product \in [ Vars: SUBSET Nat,
                  Init: Nat, Next: Nat, Termination: Nat, fairness: FAIRNESSOPS ]

PCTypeInv ==
  pc \in [PROCS -> {"ready","done"}]

TypeInv ==
  /\ AstConstInv
  /\ StageTypeInv
  /\ ErrsTypeInv
  /\ ExplodedTypeInv
  /\ RoutedTypeInv
  /\ SubscriptedTypeInv
  /\ ProductTypeInv
  /\ PCTypeInv

(***************************************************************************)
(* Liveness: termination of the translation pipeline                       *)
(***************************************************************************)

Termination ==
  <> (stage = "done")

(***************************************************************************)
(* Fairness modeling options (as used by translation output)               *)
(***************************************************************************)

Fairness_None == TRUE

Fairness_WFProc == \A p \in PROCS: WF_vars(ProcAction(p))

Fairness_WFNext == WF_vars(Next)

Fairness_SFProc == \A p \in PROCS: SF_vars(ProcAction(p))

OutFairness ==
  IF FAIRNESS = "None" THEN Fairness_None
  ELSE IF FAIRNESS = "WFProc" THEN Fairness_WFProc
  ELSE IF FAIRNESS = "WFNext" THEN Fairness_WFNext
  ELSE IF FAIRNESS = "SFProc" THEN Fairness_SFProc
  ELSE TRUE

(***************************************************************************)
(* The complete specification of this module                               *)
(***************************************************************************)

Spec ==
  Init /\ [][Next]_vars /\ OutFairness

=============================================================================