---------------------------- MODULE ArrayControlObservation ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS
    N,          \* length of the shared array (N >= 2)
    C0,         \* initial value of the control variable
    Values,     \* finite set of integer values the control variable may take
    Pos         \* array position that the update steps write to

ASSUME NAssump      == N \in Nat /\ N >= 2
ASSUME ValuesAssump == Values \subseteq Int /\ Cardinality(Values) >= 2
ASSUME C0Assump     == C0 \in Values
ASSUME PosAssump    == Pos \in 1..N

Idx == 1..N

VARIABLES
    arr,        \* shared mutable array: function Idx -> Int
    ctrl,       \* integer-valued control variable
    prevCtrl,   \* value of ctrl before the most recent update step (history)
    lastStep    \* which kind of step was taken last: "init", "seeNew", "seeOld"

vars == <<arr, ctrl, prevCtrl, lastStep>>

--------------------------------------------------------------------------------
Init ==
    /\ arr = [i \in Idx |-> i]          \* pairwise distinct initial values
    /\ ctrl = C0
    /\ prevCtrl = C0
    /\ lastStep = "init"

\* (1) Update control variable and write array using the NEW control value.
SeeNew ==
    /\ \E v \in Values \ {ctrl} :
          /\ ctrl' = v
          /\ arr' = [arr EXCEPT ![Pos] = ctrl']    \* observes the updated ctrl
    /\ prevCtrl' = ctrl
    /\ lastStep' = "seeNew"

\* (2) Update control variable identically, but array write uses the OLD value.
SeeOld ==
    /\ \E v \in Values \ {ctrl} :
          /\ ctrl' = v
          /\ arr' = [arr EXCEPT ![Pos] = ctrl]     \* must not observe new ctrl
    /\ prevCtrl' = ctrl
    /\ lastStep' = "seeOld"

\* (3) Explicit stuttering step: nothing changes.
Stutter ==
    UNCHANGED vars

Next == SeeNew \/ SeeOld \/ Stutter

Fairness == WF_vars(SeeNew) /\ WF_vars(SeeOld)

Spec == Init /\ [][Next]_vars /\ Fairness

--------------------------------------------------------------------------------
\* Safety: type invariant -- array is always a mapping from the index set to Int
TypeOK ==
    /\ arr \in [Idx -> Int]
    /\ ctrl \in Values
    /\ prevCtrl \in Values
    /\ lastStep \in {"init", "seeNew", "seeOld"}

ArrayIsIntMapping == arr \in [Idx -> Int]

\* Safety: after a SeeNew step the entry reflects the new control value
SeeNewCorrect ==
    lastStep = "seeNew" => arr[Pos] = ctrl

\* Safety: after a SeeOld step the entry still reflects the old control value
SeeOldCorrect ==
    lastStep = "seeOld" => (arr[Pos] = prevCtrl /\ arr[Pos] # ctrl)

\* The two behaviors are observably distinct
StepsDistinguishable ==
    (lastStep = "seeNew" => arr[Pos] # prevCtrl)

Invariants ==
    /\ TypeOK
    /\ ArrayIsIntMapping
    /\ SeeNewCorrect
    /\ SeeOldCorrect
    /\ StepsDistinguishable

\* Action-level safety properties for the respective steps
SeeNewActionProp ==
    [][SeeNew => (arr'[Pos] = ctrl' /\ ctrl' # ctrl)]_vars

SeeOldActionProp ==
    [][SeeOld => (arr'[Pos] = ctrl /\ arr'[Pos] # ctrl')]_vars

\* Other array positions are never affected by either update step
FrameProp ==
    [][(SeeNew \/ SeeOld) => \A i \in Idx \ {Pos} : arr'[i] = arr[i]]_vars

\* Both update steps are possible from the initial state
BothEnabledInitially ==
    Init => (ENABLED SeeNew /\ ENABLED SeeOld)

\* Liveness: each kind of update step is eventually (repeatedly) exercised
SeeNewOccurs == []<>(lastStep = "seeNew")
SeeOldOccurs == []<>(lastStep = "seeOld")

THEOREM Spec => []Invariants
THEOREM Spec => SeeNewActionProp /\ SeeOldActionProp /\ FrameProp
THEOREM Spec => SeeNewOccurs /\ SeeOldOccurs
=============================================================================