------------------------------- MODULE EuclidGCD -------------------------------
(***************************************************************************)
(* Euclid's algorithm (subtraction form) computing GCD(24, y0), where y0   *)
(* is chosen nondeterministically from 1..N. Check with N = 3.             *)
(*                                                                         *)
(* Suggested TLC configuration:                                            *)
(*   CONSTANT N = 3                                                        *)
(*   SPECIFICATION Spec                                                    *)
(*   INVARIANTS TypeOK GCDPreserved Correctness                            *)
(*   PROPERTIES Termination                                                *)
(***************************************************************************)
EXTENDS Naturals, TLC

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

FirstInput == 24

VARIABLES x, y, y0, pc

vars == <<x, y, y0, pc>>

(***************************************************************************)
(* Mathematical definition of the greatest common divisor.                 *)
(***************************************************************************)
Divides(d, n) == \E k \in 0..n : n = d * k

Divisors(n) == {d \in 1..n : Divides(d, n)}

Max(S) == CHOOSE m \in S : \A s \in S : s <= m

GCD(a, b) == Max(Divisors(a) \cap Divisors(b))

(***************************************************************************)
(* Algorithm                                                               *)
(***************************************************************************)
Init == /\ x = FirstInput
        /\ y0 \in 1..N
        /\ y = y0
        /\ pc = "loop"

\* Subtract the smaller value from the larger while both are nonzero.
Step == /\ pc = "loop"
        /\ x # 0
        /\ y # 0
        /\ IF x < y
              THEN /\ y' = y - x
                   /\ x' = x
              ELSE /\ x' = x - y
                   /\ y' = y
        /\ UNCHANGED <<y0, pc>>

\* One value has reached zero: the other holds the GCD. Print and stop.
Finish == /\ pc = "loop"
          /\ (x = 0 \/ y = 0)
          /\ PrintT(<<"GCD(24, y0): y0 =", y0, "result =", x + y,
                      "expected =", GCD(FirstInput, y0)>>)
          /\ pc' = "Done"
          /\ UNCHANGED <<x, y, y0>>

\* Allow infinite stuttering after termination (avoids deadlock reports).
Terminated == /\ pc = "Done"
              /\ UNCHANGED vars

Next == Step \/ Finish \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)
TypeOK == /\ x \in 0..FirstInput
          /\ y \in 0..N
          /\ y0 \in 1..N
          /\ pc \in {"loop", "Done"}

\* The GCD of the current pair always equals the GCD of the original inputs
\* (while both values are positive).
GCDPreserved == (x # 0 /\ y # 0) => GCD(x, y) = GCD(FirstInput, y0)

\* When the algorithm finishes, the nonzero value is the correct GCD.
Correctness == (pc = "Done") => (x + y = GCD(FirstInput, y0))

(***************************************************************************)
(* Liveness: the algorithm always terminates, for every initial y0.        *)
(***************************************************************************)
Termination == <>(pc = "Done")

=============================================================================