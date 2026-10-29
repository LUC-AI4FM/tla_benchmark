---------------------------- MODULE IterativeSquares ----------------------------
(***************************************************************************)
(* Computes the squares of all integers from 1 to N using only addition,   *)
(* exploiting the identity  n^2 = (n-1)^2 + (2n - 1),  i.e. every perfect  *)
(* square is a sum of consecutive odd numbers.                             *)
(*                                                                         *)
(* PlusCal-style sketch:                                                   *)
(*   x := 0; odd := 1; i := 0; f := [k \in 1..N |-> 0];                    *)
(*   while (i < N) {                                                       *)
(*      x := x + odd; odd := odd + 2; i := i + 1; f[i] := x;               *)
(*   }                                                                     *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat

VARIABLES i,    \* number of squares computed so far (loop counter)
          x,    \* current accumulated square, x = i^2
          odd,  \* next odd number to add, odd = 2i + 1
          f,    \* result array: f[k] = k^2 for k \in 1..i
          pc    \* program counter

vars == <<i, x, odd, f, pc>>

-----------------------------------------------------------------------------

TypeOK ==
    /\ i \in 0..N
    /\ x \in Nat
    /\ odd \in Nat
    /\ f \in [1..N -> Nat]
    /\ pc \in {"Loop", "Done"}

Init ==
    /\ i = 0
    /\ x = 0
    /\ odd = 1
    /\ f = [k \in 1..N |-> 0]
    /\ pc = "Loop"

(* One loop iteration: add the next odd number to the previous square. *)
Step ==
    /\ pc = "Loop"
    /\ i < N
    /\ x' = x + odd
    /\ odd' = odd + 2
    /\ i' = i + 1
    /\ f' = [f EXCEPT ![i + 1] = x + odd]
    /\ pc' = "Loop"

(* Loop exit: all requested squares have been computed. *)
Finish ==
    /\ pc = "Loop"
    /\ i >= N
    /\ pc' = "Done"
    /\ UNCHANGED <<i, x, odd, f>>

(* Allow stuttering after termination to avoid deadlock reports. *)
Terminated ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Step \/ Finish \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Step \/ Finish)

-----------------------------------------------------------------------------
(* Safety properties *)

(* Loop invariant: the recurrence has been applied correctly so far. *)
LoopInvariant ==
    /\ x = i * i
    /\ odd = 2 * i + 1
    /\ \A k \in 1..i : f[k] = k * k

(* Each computed entry satisfies n^2 = (n-1)^2 + (2n - 1). *)
RecurrenceHolds ==
    \A k \in 2..i : f[k] = f[k - 1] + (2 * k - 1)

(* Correctness of results: upon termination, f[k] = k^2 for all k. *)
Correctness ==
    pc = "Done" => /\ i = N
                   /\ \A k \in 1..N : f[k] = k * k

-----------------------------------------------------------------------------
(* Liveness properties *)

(* The algorithm always terminates. *)
Termination == <>(pc = "Done")

(* Once terminated, the results are correct and stay correct. *)
EventuallyCorrect == <>[](pc = "Done" /\ \A k \in 1..N : f[k] = k * k)

=============================================================================