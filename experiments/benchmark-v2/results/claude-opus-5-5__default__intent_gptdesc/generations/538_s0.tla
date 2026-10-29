--------------------------- MODULE SquareByOddSums ---------------------------
(***************************************************************************)
(* Computes the square of a nonnegative integer N by summing the first     *)
(* N odd numbers: 1 + 3 + ... + (2N - 1) = N^2.                            *)
(*                                                                         *)
(* Each iteration has two steps: first increment the counter k, then add   *)
(* the k-th odd number (2*k - 1) to the running total.                     *)
(* After termination the system may only stutter.                          *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT Inputs                \* nonempty set of allowed input values

ASSUME InputsAssumption == /\ Inputs \subseteq Nat
                           /\ Inputs # {}

VARIABLES input,   \* the natural number whose square is computed
          i,       \* iteration counter
          total,   \* running total
          pc       \* control state: "loop", "add", or "done"

vars == <<input, i, total, pc>>

(***************************************************************************)
(* Sum of the first k odd numbers: 1 + 3 + ... + (2k - 1).                 *)
(***************************************************************************)
RECURSIVE SumOdd(_)
SumOdd(k) == IF k = 0 THEN 0 ELSE SumOdd(k - 1) + (2 * k - 1)

(***************************************************************************)
(* Number of iterations completed so far. When pc = "add", the counter     *)
(* has been incremented but the total has not yet been updated.            *)
(***************************************************************************)
Completed == IF pc = "add" THEN i - 1 ELSE i

-----------------------------------------------------------------------------
TypeOK == /\ input \in Inputs
          /\ i \in Nat
          /\ total \in Nat
          /\ pc \in {"loop", "add", "done"}

Init == /\ input \in Inputs
        /\ i = 0
        /\ total = 0
        /\ pc = "loop"

(* Loop test succeeds: increment the counter. *)
Increment == /\ pc = "loop"
             /\ i < input
             /\ i' = i + 1
             /\ pc' = "add"
             /\ UNCHANGED <<input, total>>

(* Add the next odd number 2*k - 1 for the current counter value k. *)
AddOdd == /\ pc = "add"
          /\ total' = total + (2 * i - 1)
          /\ pc' = "loop"
          /\ UNCHANGED <<input, i>>

(* Loop test fails: terminate. *)
Finish == /\ pc = "loop"
          /\ i >= input
          /\ pc' = "done"
          /\ UNCHANGED <<input, i, total>>

(* After termination, allow stuttering so termination is not deadlock. *)
Terminated == /\ pc = "done"
              /\ UNCHANGED vars

Next == Increment \/ AddOdd \/ Finish \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

(* The running total always equals the sum of the odd numbers for the      *)
(* completed iterations (hence equals Completed^2).                        *)
SumInvariant == /\ total = SumOdd(Completed)
                /\ total = Completed * Completed
                /\ Completed <= input
                /\ (pc = "add") => (i >= 1)

(* No step ever changes the input value. *)
InputUnchanged == [][input' = input]_vars

(* Partial correctness: upon termination, total = input^2 and i = input. *)
Correctness == (pc = "done") => /\ total = input * input
                                /\ i = input

(* Correctness stated relative to the initial input value. *)
CorrectnessForInitialInput ==
    \A n \in Inputs :
        (input = n) => [](pc = "done" => /\ total = n * n
                                         /\ i = n)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness: eventual termination for every allowed input value.           *)
(***************************************************************************)
Termination == <>(pc = "done")

TerminationForEveryInput ==
    \A n \in Inputs : (input = n) => <>(pc = "done")

(* Once terminated, the system stays terminated. *)
StaysTerminated == [](pc = "done" => [](pc = "done"))

-----------------------------------------------------------------------------
THEOREM Spec => /\ []TypeOK
                /\ []SumInvariant
                /\ []Correctness
                /\ InputUnchanged
                /\ CorrectnessForInitialInput
                /\ Termination
                /\ TerminationForEveryInput
                /\ StaysTerminated
=============================================================================