------------------------------ MODULE SimpleStateMachine ------------------------------
EXTENDS Naturals, Integers

CONSTANTS MaxX, MaxY

ASSUME MaxX \in Nat /\ MaxX >= 2
ASSUME MaxY \in Nat /\ MaxY >= 1

VARIABLES x, y

vars == <<x, y>>

TypeOK ==
    /\ x \in Int
    /\ y \in Int

-----------------------------------------------------------------------------
(* Initial state: each component is constrained independently. *)

Init ==
    /\ x \in 0..2
    /\ y \in {0, 1}

-----------------------------------------------------------------------------
(* Transition kinds                                                          *)

(* (a) Update x only. y is left unchanged and referenced individually. *)
IncX ==
    /\ x < MaxX
    /\ x' = x + 1
    /\ UNCHANGED y

(* (a) Update y only. x is left unchanged and referenced individually. *)
IncY ==
    /\ y < MaxY
    /\ y' = y + 1
    /\ UNCHANGED x

(* (b) Update both components with concrete numeric expressions. *)
IncBoth ==
    /\ x < MaxX
    /\ y < MaxY
    /\ x' = x + 1
    /\ y' = y + 1

(* (b) Update both components at once. The assignment is guarded and keeps the state within bounds. *)
SwapLike ==
    /\ x <= MaxY
    /\ y <= MaxX
    /\ x /= y
    /\ x' = y
    /\ y' = x

(* (c) Guarded stutter. Both components are grouped as a tuple. *)
HoldTuple ==
    /\ x = MaxX
    /\ UNCHANGED <<x, y>>

(* (c) Guarded stutter. The components are referenced individually. *)
HoldSeparate ==
    /\ y = MaxY
    /\ UNCHANGED x
    /\ UNCHANGED y

(* (c) Guarded stutter. The grouping is expressed through vars. *)
HoldVars ==
    /\ x + y >= MaxX + MaxY
    /\ UNCHANGED vars

(* Unreachable: the numeric guard can never hold in a reachable state. *)
ResetX ==
    /\ x > MaxX + 100
    /\ x' = 0
    /\ UNCHANGED y

(* Unreachable: the guard is contradictory. *)
NeverStep ==
    /\ x < 0
    /\ x > 0
    /\ x' = x
    /\ y' = y + 1

(* Unreachable: the guard is trivially false. *)
DeadStep ==
    /\ FALSE
    /\ UNCHANGED <<x, y>>

Next ==
    \/ IncX
    \/ IncY
    \/ IncBoth
    \/ SwapLike
    \/ HoldTuple
    \/ HoldSeparate
    \/ HoldVars
    \/ ResetX
    \/ NeverStep
    \/ DeadStep

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* State constraint that bounds the execution, usable as a TLC CONSTRAINT. *)

StateBound == x <= MaxX /\ y <= MaxY

-----------------------------------------------------------------------------
(* Temporal safety property: every step conforms to one of the alternatives. *)

StepsConform == [][Next]_vars

-----------------------------------------------------------------------------
(* (1) Invariants on numeric bounds *)

BoundX     == x \in 0..MaxX
BoundY     == y \in 0..MaxY
NonNeg     == x >= 0 /\ y >= 0
SumBounded == x + y <= MaxX + MaxY

Inv == TypeOK /\ BoundX /\ BoundY /\ NonNeg /\ SumBounded

-----------------------------------------------------------------------------
(* (2) Unreachable guarded transitions are never enabled and never taken *)

ResetXNeverEnabled    == ~ENABLED ResetX
NeverStepNeverEnabled == ~ENABLED NeverStep
DeadStepNeverEnabled  == ~ENABLED DeadStep

UnreachableInv ==
    /\ ResetXNeverEnabled
    /\ NeverStepNeverEnabled
    /\ DeadStepNeverEnabled

ResetXNeverTaken    == [][~ResetX]_vars
NeverStepNeverTaken == [][~NeverStep]_vars
DeadStepNeverTaken  == [][~DeadStep]_vars

-----------------------------------------------------------------------------
(* (3) UNCHANGED means no change to the intended components *)

IncXKeepsY ==
    [][IncX => (y' = y /\ x' /= x)]_vars

IncYKeepsX ==
    [][IncY => (x' = x /\ y' /= y)]_vars

HoldTupleKeepsAll ==
    [][HoldTuple => (x' = x /\ y' = y)]_vars

HoldSeparateKeepsAll ==
    [][HoldSeparate => (<<x, y>>' = <<x, y>>)]_vars

HoldVarsKeepsAll ==
    [][HoldVars => (x' = x /\ y' = y /\ vars' = vars)]_vars

UnchangedEquivalence ==
    [][(UNCHANGED <<x, y>>) <=> (UNCHANGED x /\ UNCHANGED y)]_vars

UnchangedCorrect ==
    /\ IncXKeepsY
    /\ IncYKeepsX
    /\ HoldTupleKeepsAll
    /\ HoldSeparateKeepsAll
    /\ HoldVarsKeepsAll
    /\ UnchangedEquivalence

-----------------------------------------------------------------------------
(* Coverage support                                                          *)
(* Each transition is a separately named action, so TLC's per-action and    *)
(* per-subexpression coverage can report on transitions and on individual   *)
(* occurrences of x and y. The model does not say how transitions are       *)
(* implemented.                                                             *)

THEOREM Spec => []Inv
THEOREM Spec => []UnreachableInv
THEOREM Spec => StepsConform
THEOREM Spec => ResetXNeverTaken /\ NeverStepNeverTaken /\ DeadStepNeverTaken
THEOREM Spec => UnchangedCorrect

=============================================================================