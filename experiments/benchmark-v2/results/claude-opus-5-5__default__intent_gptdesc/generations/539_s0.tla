---------------------------- MODULE SquaresArray ----------------------------
(***************************************************************************)
(* An iterative algorithm that fills an array a[0..N] so that, on          *)
(* termination, a[j] = j * j for every index j.                            *)
(*                                                                         *)
(* Control states:                                                         *)
(*   "before" : about to update a[i]                                       *)
(*   "after"  : a[i] has just been updated                                 *)
(*   "done"   : the loop has terminated                                    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    N,        \* the last index of the array (array has length N+1)
    MaxInt    \* upper bound on safe numeric values

ASSUME NAssumption      == N \in Nat
ASSUME MaxIntAssumption == MaxInt \in Nat /\ N * N <= MaxInt

VARIABLES
    i,     \* current index
    a,     \* the array, a function from 0..N to values
    pc     \* control state

vars == << i, a, pc >>

Indexes    == 0 .. N
Values     == 0 .. MaxInt
PCs        == {"before", "after", "done"}

-----------------------------------------------------------------------------
(* Initial state: index 0, array holds arbitrary values in the safe range. *)

Init ==
    /\ i  = 0
    /\ a  \in [Indexes -> Values]
    /\ pc = "before"

-----------------------------------------------------------------------------
(* Actions *)

\* Write the square of the current index into the array.
Update ==
    /\ pc = "before"
    /\ a'  = [a EXCEPT ![i] = i * i]
    /\ pc' = "after"
    /\ UNCHANGED i

\* Advance to the next index while more indexes remain.
Advance ==
    /\ pc = "after"
    /\ i < N
    /\ i'  = i + 1
    /\ pc' = "before"
    /\ UNCHANGED a

\* Leave the loop once the last index has been processed.
Finish ==
    /\ pc = "after"
    /\ i = N
    /\ pc' = "done"
    /\ UNCHANGED << i, a >>

\* Once finished, the system stutters (prevents deadlock reports).
Terminated ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ Update
    \/ Advance
    \/ Finish
    \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Update \/ Advance \/ Finish)

-----------------------------------------------------------------------------
(* (1) Type safety: all variables stay within their declared domains. *)

TypeOK ==
    /\ i  \in Indexes
    /\ a  \in [Indexes -> Values]
    /\ pc \in PCs

(* (2) Partial correctness: the processed prefix holds correct squares. *)

PartialCorrectness ==
    /\ pc = "before" => \A j \in 0 .. (i - 1) : a[j] = j * j
    /\ pc = "after"  => \A j \in 0 .. i       : a[j] = j * j

\* After each update step the processed portion is correct.
UpdateStepCorrect ==
    [][Update => \A j \in 0 .. i : a'[j] = j * j]_vars

(* (3) Final correctness: the postcondition holds upon termination. *)

Postcondition ==
    pc = "done" =>
        /\ i = N
        /\ \A j \in Indexes : a[j] = j * j

(* Legal control-state transitions only. *)

LegalTransitions ==
    [][ \/ (pc = "before" /\ pc' = "after")
        \/ (pc = "after"  /\ pc' = "before" /\ i' = i + 1)
        \/ (pc = "after"  /\ pc' = "done"   /\ i = N)
      ]_vars

\* Once done, the system remains done.
DoneIsStable == [](pc = "done" => [](pc = "done"))

(* Combined safety invariant. *)

Inv ==
    /\ TypeOK
    /\ PartialCorrectness
    /\ Postcondition

-----------------------------------------------------------------------------
(* (4) Liveness / termination *)

Termination == <>(pc = "done")

CorrectTermination ==
    <>(pc = "done" /\ i = N /\ \A j \in Indexes : a[j] = j * j)

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []PartialCorrectness
THEOREM Spec => []Postcondition
THEOREM Spec => UpdateStepCorrect
THEOREM Spec => LegalTransitions
THEOREM Spec => Termination
THEOREM Spec => CorrectTermination
=============================================================================