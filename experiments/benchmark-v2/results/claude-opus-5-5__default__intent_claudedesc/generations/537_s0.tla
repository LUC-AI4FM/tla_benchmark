---------------------------- MODULE IntegerSquaring ----------------------------
(***************************************************************************)
(* Iterative computation of N^2 using only addition, by summing the first  *)
(* N odd numbers: 1 + 3 + 5 + ... + (2N-1) = N^2.                          *)
(*                                                                         *)
(*   i := 0; sq := 0;                                                      *)
(*   while (i < N) { sq := sq + (i + i + 1); i := i + 1 }                  *)
(*                                                                         *)
(* The odd number 2i+1 is formed as i + i + 1, so the loop body uses no    *)
(* multiplication.                                                         *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat

VARIABLES n, i, sq, pc

vars == <<n, i, sq, pc>>

\* Multiplication appears only in the properties, never in the algorithm.
Square(x) == x * x

-----------------------------------------------------------------------------

Init == /\ n = N
        /\ i = 0
        /\ sq = 0
        /\ pc = "loop"

\* Loop body: add the next odd number, then advance the counter.
Step == /\ pc = "loop"
        /\ i < n
        /\ sq' = sq + (i + i + 1)
        /\ i' = i + 1
        /\ UNCHANGED <<n, pc>>

\* Loop exit.
Finish == /\ pc = "loop"
          /\ ~(i < n)
          /\ pc' = "done"
          /\ UNCHANGED <<n, i, sq>>

\* Lets the finished algorithm stutter, so TLC reports no deadlock.
Terminated == /\ pc = "done"
              /\ UNCHANGED vars

Next == Step \/ Finish \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Step \/ Finish)

-----------------------------------------------------------------------------
(* Safety properties *)

\* Type safety and bounds on every variable.
TypeOK == /\ n \in Nat
          /\ n = N
          /\ i \in 0..n
          /\ sq \in 0..Square(n)
          /\ pc \in {"loop", "done"}

\* Loop invariant: the accumulator is the square of the progress so far.
LoopInvariant == sq = Square(i)

\* Partial correctness: on termination, the result is n^2.
PartialCorrectness == (pc = "done") => (sq = Square(n))

\* Termination state: the counter has reached the input and the result is complete.
TerminationState == (pc = "done") => (i = n /\ sq = Square(n))

\* Conjunction of all safety invariants.
Inv == TypeOK /\ LoopInvariant /\ PartialCorrectness /\ TerminationState

-----------------------------------------------------------------------------
(* Liveness properties *)

\* The algorithm eventually terminates.
Termination == <>(pc = "done")

\* The algorithm eventually terminates with the correct result.
TotalCorrectness == <>(pc = "done" /\ sq = Square(n) /\ i = n)

-----------------------------------------------------------------------------

THEOREM Spec => []Inv
THEOREM Spec => Termination
THEOREM Spec => TotalCorrectness

(* Example model configuration (IntegerSquaring.cfg):
     CONSTANT N = 5
     SPECIFICATION Spec
     INVARIANTS TypeOK LoopInvariant PartialCorrectness TerminationState
     PROPERTIES Termination TotalCorrectness
*)
=============================================================================