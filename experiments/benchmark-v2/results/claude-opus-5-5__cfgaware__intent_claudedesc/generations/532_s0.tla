---------------------------- MODULE Exponentiation ----------------------------
EXTENDS Integers, Naturals

CONSTANTS MSet, NSet

ASSUME MSet \subseteq Int
ASSUME NSet \subseteq Nat

VARIABLES m, n, r, i, pc

vars == <<m, n, r, i, pc>>

RECURSIVE Pow(_, _)
Pow(b, e) == IF e = 0 THEN 1 ELSE b * Pow(b, e - 1)

TypeOK ==
    /\ m \in Int
    /\ n \in Nat
    /\ r \in Int
    /\ i \in Nat
    /\ pc \in {"check", "loop", "Done"}

Init ==
    /\ m \in MSet
    /\ n \in NSet
    /\ r = 1
    /\ i = 0
    /\ pc = "check"

Check ==
    /\ pc = "check"
    /\ Assert(m \in Int /\ n \in Nat, "Input constraints violated")
    /\ pc' = "loop"
    /\ UNCHANGED <<m, n, r, i>>

Loop ==
    /\ pc = "loop"
    /\ IF i < n
         THEN /\ r' = r * m
              /\ i' = i + 1
              /\ pc' = "loop"
         ELSE /\ pc' = "Done"
              /\ UNCHANGED <<r, i>>
    /\ UNCHANGED <<m, n>>

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Check \/ Loop \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Check \/ Loop)

Assert(cond, msg) == cond

InputOK == (pc = "check") => (m \in Int /\ n \in Nat)

Invariant == /\ i <= n
             /\ r = Pow(m, i)

PartialCorrectness == (pc = "Done") => (r = Pow(m, n))

Termination == <>(pc = "Done")

=============================================================================