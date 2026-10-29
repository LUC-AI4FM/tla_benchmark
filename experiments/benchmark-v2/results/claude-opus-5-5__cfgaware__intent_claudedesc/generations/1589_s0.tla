---------------------------- MODULE Euclid ----------------------------
EXTENDS Naturals, TLC

N == 20

ASSUME N \in Nat \ {0}

VARIABLES u, v, u_ini, v_ini, pc

vars == << u, v, u_ini, v_ini, pc >>

\* Naive mathematical definition of GCD
Divides(p, n) == \E q \in 0..n : n = q * p

DivisorsOf(n) == { p \in 1..n : Divides(p, n) }

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))

TypeOK ==
    /\ u \in 0..N
    /\ v \in 1..N
    /\ u_ini \in 1..N
    /\ v_ini \in 1..N
    /\ pc \in {"Loop", "Done"}

Init ==
    /\ u_ini \in 1..N
    /\ v_ini \in 1..N
    /\ u = u_ini
    /\ v = v_ini
    /\ pc = "Loop"

\* One iteration of the subtraction-based loop:
\* if u < v then swap; then u := u - v
Step ==
    /\ pc = "Loop"
    /\ u # 0
    /\ IF u < v
          THEN /\ u' = v - u
               /\ v' = u
          ELSE /\ u' = u - v
               /\ v' = v
    /\ pc' = "Loop"
    /\ UNCHANGED << u_ini, v_ini >>

Exit ==
    /\ pc = "Loop"
    /\ u = 0
    /\ pc' = "Done"
    /\ UNCHANGED << u, v, u_ini, v_ini >>

\* Allow stuttering once terminated so TLC does not report deadlock
Terminated ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Step \/ Exit \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Step \/ Exit)

-----------------------------------------------------------------------------

Finished == pc = "Done"

SwapOccurs == pc = "Loop" /\ u # 0 /\ u < v

\* Safety: upon termination the result is the true GCD of the inputs
Invariant == Finished => v = GCD(u_ini, v_ini)

\* Liveness: the algorithm always eventually terminates
Termination == <>Finished

\* Possibility-style properties (all hold under Spec)
_POSSIBLE == <>Finished /\ [](Finished => u = 0)

PossibleCounts == [](u_ini \in 1..N /\ v_ini \in 1..N) /\ <>[]Finished

=============================================================================