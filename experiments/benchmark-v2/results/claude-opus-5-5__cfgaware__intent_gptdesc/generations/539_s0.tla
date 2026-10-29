---------------------------- MODULE SquareArray ----------------------------
EXTENDS Naturals

(***************************************************************************)
(* A simple iterative computation that fills an array a[0..n] with the    *)
(* squares of its indices.                                                *)
(*                                                                         *)
(* Control states:                                                         *)
(*   "before" : about to update a[i]                                       *)
(*   "after"  : a[i] has just been updated                                 *)
(*   "done"   : the loop has terminated                                    *)
(***************************************************************************)

VARIABLES n, i, a, pc

vars == <<n, i, a, pc>>

\* The set of allowed values of n: any nonnegative integer.
NSet == Nat

\* A finite substitute for NSet, used for model checking.
ConstNSet == 0..3

PCs == {"before", "after", "done"}

TypeOK ==
    /\ n \in NSet
    /\ i \in 0..n
    /\ a \in [0..n -> 0..(n * n)]
    /\ pc \in PCs

Init ==
    /\ n \in NSet
    /\ i = 0
    /\ a \in [0..n -> 0..(n * n)]
    /\ pc = "before"

\* Compute the square of the current index.
Update ==
    /\ pc = "before"
    /\ a' = [a EXCEPT ![i] = i * i]
    /\ pc' = "after"
    /\ UNCHANGED <<n, i>>

\* Advance the index, or finish the loop.
Advance ==
    /\ pc = "after"
    /\ IF i < n
         THEN /\ i' = i + 1
              /\ pc' = "before"
         ELSE /\ i' = i
              /\ pc' = "done"
    /\ UNCHANGED <<n, a>>

\* Once finished, the system only stutters.
Finished ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Update \/ Advance \/ Finished

Spec == Init /\ [][Next]_vars /\ WF_vars(Update \/ Advance)

-----------------------------------------------------------------------------
\* Correctness properties

\* Every cell in 0..k holds the square of its index.
PrefixCorrect(k) == \A j \in 0..k : a[j] = j * j

\* Partial correctness: the processed portion of the array is correct.
ReachableStateInv ==
    /\ TypeOK
    /\ (pc = "before") => (\A j \in 0..n : j < i => a[j] = j * j)
    /\ (pc = "after")  => PrefixCorrect(i)
    /\ (pc = "done")   => (i = n /\ PrefixCorrect(n))

\* Postcondition: upon termination, every entry equals its index squared.
SquareCorrect ==
    (pc = "done") => (i = n /\ \A j \in 0..n : a[j] = j * j)

\* Liveness: the algorithm eventually terminates.
Termination == <>(pc = "done")

=============================================================================