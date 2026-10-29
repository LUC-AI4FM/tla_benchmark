---------------------------- MODULE EuclidGCD ----------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME NAssump == (N \in Nat) /\ (N = 20)

(***************************************************************************)
(* Naive mathematical definition of the greatest common divisor.           *)
(***************************************************************************)
Divides(p, n) == \E q \in 1..n : n = q * p

DivisorsOf(n) == {p \in 1..n : Divides(p, n)}

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))

(***************************************************************************)
(* x, y  : the working values of the algorithm                             *)
(* x0, y0: the original inputs (kept to state correctness)                 *)
(***************************************************************************)
VARIABLES x, y, x0, y0

vars == <<x, y, x0, y0>>

TypeOK ==
    /\ x \in 0..N
    /\ y \in 1..N
    /\ x0 \in 1..N
    /\ y0 \in 1..N

Init ==
    /\ x0 \in 1..N
    /\ y0 \in 1..N
    /\ x = x0
    /\ y = y0

(***************************************************************************)
(* One iteration: if the smaller value is in the first position, swap;     *)
(* then subtract the second value from the first.                          *)
(***************************************************************************)
Step ==
    /\ x # 0
    /\ IF x < y
         THEN /\ x' = y - x
              /\ y' = x
         ELSE /\ x' = x - y
              /\ y' = y
    /\ UNCHANGED <<x0, y0>>

(***************************************************************************)
(* Once the first value reaches zero the algorithm has terminated; we      *)
(* allow stuttering to avoid a TLC deadlock report.                        *)
(***************************************************************************)
Terminated ==
    /\ x = 0
    /\ UNCHANGED vars

Next == Step \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

(***************************************************************************)
(* Safety: upon termination, y holds the GCD of the original inputs.       *)
(***************************************************************************)
Correctness == (x = 0) => (y = GCD(x0, y0))

(***************************************************************************)
(* Liveness: the algorithm always eventually terminates.                   *)
(***************************************************************************)
Termination == <>(x = 0)

THEOREM Spec => [](TypeOK /\ Correctness)
THEOREM Spec => Termination
=============================================================================