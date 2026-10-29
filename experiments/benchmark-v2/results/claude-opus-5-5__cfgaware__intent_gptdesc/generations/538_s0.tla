---------------------------- MODULE SquareBySumOfOdds ----------------------------
EXTENDS Naturals

CONSTANT NSet

ASSUME NSetAssump == NSet \subseteq Nat /\ NSet # {}

VARIABLES x, n, i, a, b, pc

vars == << x, n, i, a, b, pc >>

(* x  : the input value, chosen once from NSet and never changed          *)
(* n  : working copy of the input, used as the loop bound                 *)
(* i  : iteration counter                                                 *)
(* b  : the odd number 2*i - 1 for the current counter value              *)
(* a  : running total (sum of the first i odd numbers)                    *)
(* pc : control location                                                  *)

SumOdds(k) == LET f[m \in Nat] == IF m = 0 THEN 0 ELSE f[m-1] + (2*m - 1)
              IN f[k]

TypeOK ==
    /\ x \in NSet
    /\ n \in Nat
    /\ i \in Nat
    /\ a \in Nat
    /\ b \in Nat
    /\ pc \in {"loop", "inc", "add", "Done"}

Init ==
    /\ x \in NSet
    /\ n = x
    /\ i = 0
    /\ a = 0
    /\ b = 0
    /\ pc = "loop"

Loop ==
    /\ pc = "loop"
    /\ IF i < n
          THEN pc' = "inc"
          ELSE pc' = "Done"
    /\ UNCHANGED << x, n, i, a, b >>

Inc ==
    /\ pc = "inc"
    /\ i' = i + 1
    /\ b' = 2 * (i + 1) - 1
    /\ pc' = "add"
    /\ UNCHANGED << x, n, a >>

Add ==
    /\ pc = "add"
    /\ a' = a + b
    /\ pc' = "loop"
    /\ UNCHANGED << x, n, i, b >>

(* Allow infinite stuttering after termination, so it is not a deadlock *)
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Loop \/ Inc \/ Add \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Properties *)

Termination == <>(pc = "Done")

\* Running total equals the sum of odd numbers for completed iterations
Inv ==
    /\ TypeOK
    /\ i <= n
    /\ (pc \in {"loop", "inc", "Done"}) => a = SumOdds(i)
    /\ (pc = "add") => (a + b = SumOdds(i) /\ b = 2*i - 1)

\* Equivalent strengthened form: total is the square of completed count
SquareInv ==
    (pc \in {"loop", "inc", "Done"}) => a = i * i

\* No step ever changes the input value
InputUnchanged == [][x' = x /\ n' = n]_vars

\* Correctness on termination
Correctness ==
    (pc = "Done") => (a = x * x /\ i = x)

PartialCorrectness == [](Correctness)

=============================================================================