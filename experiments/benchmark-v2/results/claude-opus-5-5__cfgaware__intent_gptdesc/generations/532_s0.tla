---------------------------- MODULE IterativePower ----------------------------
EXTENDS Integers

CONSTANTS MSet, NSet

ASSUME MSet \subseteq Int
ASSUME NSet \subseteq Nat

VARIABLES m, n, prod, cnt, pc

vars == <<m, n, prod, cnt, pc>>

RECURSIVE Pow(_, _)
Pow(b, e) == IF e = 0 THEN 1 ELSE b * Pow(b, e - 1)

-----------------------------------------------------------------------------

Init ==
    /\ m \in MSet
    /\ n \in NSet
    /\ prod = 1
    /\ cnt = 0
    /\ pc = "running"

Step ==
    /\ pc = "running"
    /\ cnt < n
    /\ prod' = prod * m
    /\ cnt' = cnt + 1
    /\ UNCHANGED <<m, n, pc>>

Finish ==
    /\ pc = "running"
    /\ cnt = n
    /\ pc' = "done"
    /\ UNCHANGED <<m, n, prod, cnt>>

Halted ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Step \/ Finish \/ Halted

Spec == Init /\ [][Next]_vars /\ WF_vars(Step \/ Finish)

-----------------------------------------------------------------------------
\* Type and input safety

TypeOK ==
    /\ m \in Int
    /\ n \in Nat
    /\ prod \in Int
    /\ cnt \in Nat
    /\ pc \in {"running", "done"}

InputsSafe ==
    /\ m \in MSet
    /\ n \in NSet

\* Supporting invariants

ProdInv == prod = Pow(m, cnt)

CountBound == cnt <= n

\* Partial correctness

PartialCorrectness == (pc = "done") => (prod = Pow(m, n))

Inv ==
    /\ TypeOK
    /\ InputsSafe
    /\ ProdInv
    /\ CountBound
    /\ PartialCorrectness

\* No state corruption: inputs unchanged, count monotonically increases

InputsUnchanged == [][m' = m /\ n' = n]_vars

CountMonotonic == [][cnt' >= cnt /\ cnt' <= cnt + 1]_vars

ResultStable == [][(pc = "done") => (pc' = "done" /\ prod' = prod)]_vars

\* Progress / termination

Termination == <>(pc = "done")

TerminatesCorrectly == <>(pc = "done" /\ prod = Pow(m, n))

=============================================================================