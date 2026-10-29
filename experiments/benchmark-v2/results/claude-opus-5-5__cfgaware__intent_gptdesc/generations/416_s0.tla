---------------------------- MODULE ArrayControlUpdate ----------------------------
EXTENDS Integers, Sequences

(***************************************************************************)
(* A shared mutable array `arr` of fixed length and an independent integer *)
(* control variable `x` evolve under nondeterministic atomic steps.        *)
(*                                                                         *)
(*  - UpdateSeeNew : sets x to a new value and writes arr[1] using the     *)
(*                   NEW value of x (x').                                  *)
(*  - UpdateSeeOld : sets x to the same new value but writes arr[1] using  *)
(*                   the OLD value of x (x).                               *)
(*  - Stutter      : leaves everything unchanged.                          *)
(*                                                                         *)
(* Auxiliary history variables `lastStep` and `prevX` record which step    *)
(* last occurred and the control value before it, so that the expected    *)
(* observational outcomes can be stated as state invariants.              *)
(***************************************************************************)

VARIABLES arr, x, lastStep, prevX

vars == <<arr, x, lastStep, prevX>>

Idx == 1..2

InitArr == [i \in Idx |-> IF i = 1 THEN 10 ELSE 20]   \* distinct values
InitX   == 0

NewVal(v) == v + 1

Init ==
    /\ arr = InitArr
    /\ x = InitX
    /\ lastStep = "none"
    /\ prevX = InitX

\* (1) Array update observes the concurrently updated control value.
UpdateSeeNew ==
    /\ x' = NewVal(x)
    /\ arr' = [arr EXCEPT ![1] = x']
    /\ lastStep' = "seeNew"
    /\ prevX' = x

\* (2) Same control update, but the array update must see the old value.
UpdateSeeOld ==
    /\ x' = NewVal(x)
    /\ arr' = [arr EXCEPT ![1] = x]
    /\ lastStep' = "seeOld"
    /\ prevX' = x

\* (3) Stuttering step.
Stutter ==
    UNCHANGED vars

Next ==
    \/ UpdateSeeNew
    \/ UpdateSeeOld
    \/ Stutter

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(UpdateSeeNew)
    /\ WF_vars(UpdateSeeOld)

\* Bound the state space for model checking.
Constraint == x <= 4

-----------------------------------------------------------------------------
\* Type invariant: arr is always a mapping from the fixed index set to Int.
TypeOK ==
    /\ arr \in [Idx -> Int]
    /\ x \in Int
    /\ prevX \in Int
    /\ lastStep \in {"none", "seeNew", "seeOld"}

\* After UpdateSeeNew, the array entry reflects the new control value.
SeeNewCorrect ==
    lastStep = "seeNew" => arr[1] = x

\* After UpdateSeeOld, the array entry reflects the old control value.
SeeOldCorrect ==
    lastStep = "seeOld" => (arr[1] = prevX /\ arr[1] # x)

\* The untouched position is never modified.
OtherUnchanged ==
    arr[2] = InitArr[2]

Inv ==
    /\ TypeOK
    /\ SeeNewCorrect
    /\ SeeOldCorrect
    /\ OtherUnchanged

\* Action-level safety properties (checkable as temporal properties).
SeeNewProp == [][UpdateSeeNew => arr'[1] = x']_vars
SeeOldProp == [][UpdateSeeOld => arr'[1] = x /\ arr'[1] # x']_vars

\* Both update steps are enabled from the initial state.
BothEnabledInitially ==
    Init => (ENABLED UpdateSeeNew /\ ENABLED UpdateSeeOld)

THEOREM Spec => []Inv
=============================================================================