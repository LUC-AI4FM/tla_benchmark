---------------------------- MODULE SquareNumbers ----------------------------
(***************************************************************************)
(* A sequential algorithm that, given a nonnegative integer n, computes    *)
(* the square numbers 0^2, 1^2, ..., n^2 and stores them in an array a     *)
(* indexed by 0..n.                                                        *)
(*                                                                         *)
(* All entries start at 0. Since 0^2 = 0, entry 0 is already correct.      *)
(* The loop counter i starts at 0 and also serves as the iteration count.  *)
(* Each loop step increments i and writes the single entry a[i+1].         *)
(* The loop ends when i = n, so it runs exactly n iterations. Control      *)
(* then moves to "done".                                                   *)
(***************************************************************************)
EXTENDS Integers

CONSTANT n

ASSUME NAssumption == n \in Nat

VARIABLES
    a,        \* the array: a function from 0..n to Int
    i,        \* loop index / iteration count; entries 0..i are final
    pc,       \* control state: "loop" or "done"
    written   \* index written by the most recent step (-1 = none yet)

vars == <<a, i, pc, written>>

Indices == 0..n
NoIndex == -1

---------------------------------------------------------------------------
(* Type correctness *)

TypeOK ==
    /\ a \in [Indices -> Int]
    /\ i \in 0..n
    /\ pc \in {"loop", "done"}
    /\ written \in Indices \cup {NoIndex}

---------------------------------------------------------------------------
(* Initial state: every entry is zero, the counter is 0, control is in   *)
(* the loop, and no entry has been written yet.                          *)

Init ==
    /\ a = [k \in Indices |-> 0]
    /\ i = 0
    /\ pc = "loop"
    /\ written = NoIndex

---------------------------------------------------------------------------
(* Loop body: when i < n, deterministically write exactly one entry,     *)
(* a[i+1] := (i+1)^2, and increment the counter.                         *)

LoopStep ==
    /\ pc = "loop"
    /\ i < n
    /\ i + 1 \in Indices                      \* explicit bounds guard
    /\ a' = [a EXCEPT ![i + 1] = (i + 1) * (i + 1)]
    /\ i' = i + 1
    /\ written' = i + 1
    /\ pc' = "loop"

(* Loop exit: when i = n, move to the completed control state. *)
LoopExit ==
    /\ pc = "loop"
    /\ i = n
    /\ pc' = "done"
    /\ UNCHANGED <<a, i>>
    /\ written' = NoIndex

(* Terminal stuttering, so that the completed state is not a deadlock. *)
Terminated ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == LoopStep \/ LoopExit \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

---------------------------------------------------------------------------
(* Postcondition: entry k holds k^2 for every k in 0..n. *)

Post == \A k \in Indices : a[k] = k * k

---------------------------------------------------------------------------
(* SAFETY PROPERTIES *)

(* Bounds safety: the loop index and every written index are in 0..n.   *)
(* The array domain is never extended beyond 0..n.                       *)
BoundsSafety ==
    /\ i \in Indices
    /\ written \in Indices \cup {NoIndex}
    /\ DOMAIN a = Indices

(* Correct update invariant: entries 0..i equal 0^2..i^2.          *)
(* Entries beyond i are still untouched, so they remain 0.         *)
CorrectUpdateInv ==
    /\ \A k \in 0..i : a[k] = k * k
    /\ \A k \in (i + 1)..n : a[k] = 0

(* The iteration count never exceeds n, which bounds termination. *)
IterationBound == i <= n

(* Partial correctness: completion implies the postcondition. *)
DoneImpliesPost == (pc = "done") => (i = n /\ Post)

(* Combined state invariant. *)
Inv ==
    /\ TypeOK
    /\ BoundsSafety
    /\ CorrectUpdateInv
    /\ IterationBound
    /\ DoneImpliesPost

---------------------------------------------------------------------------
(* ACTION (STEP) PROPERTIES *)

(* Single-writer property: in every step, at most one entry changes.  *)
(* Any changed entry is exactly the documented index written', which  *)
(* lies within bounds.                                                *)
SingleWriterStep ==
    /\ \A k \in Indices : (a'[k] # a[k]) => (k = written' /\ written' \in Indices)
    /\ \A k1, k2 \in Indices :
           (a'[k1] # a[k1] /\ a'[k2] # a[k2]) => k1 = k2

SingleWriter == [][SingleWriterStep]_vars

(* Every loop update writes exactly one in-bounds entry with the right value. *)
UpdateStepCorrect ==
    [][LoopStep => /\ written' \in Indices
                   /\ a'[written'] = written' * written'
                   /\ \A k \in Indices \ {written'} : a'[k] = a[k]]_vars

(* The iteration count increases monotonically, by at most one per step. *)
MonotonicCounter == [][i' >= i /\ i' <= i + 1]_vars

(* Once completed, control stays completed and the array is frozen. *)
DoneIsStable == [][(pc = "done") => (pc' = "done" /\ a' = a)]_vars

---------------------------------------------------------------------------
(* LIVENESS PROPERTIES *)

(* Termination: control eventually reaches "done" with the postcondition. *)
Termination == <>(pc = "done" /\ Post)

(* Once reached, completion with the postcondition holds forever. *)
EventuallyAlwaysDone == <>[](pc = "done" /\ Post)

---------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => SingleWriter
THEOREM Spec => UpdateStepCorrect
THEOREM Spec => MonotonicCounter
THEOREM Spec => DoneIsStable
THEOREM Spec => Termination
THEOREM Spec => EventuallyAlwaysDone
=============================================================================