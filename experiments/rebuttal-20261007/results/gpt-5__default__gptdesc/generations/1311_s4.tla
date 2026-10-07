----------------------------- MODULE GCDSubSwap -----------------------------
EXTENDS Naturals, Integers

CONSTANTS U0, VMax

ASSUME U0 = 24 /\ VMax = 50

VARIABLES u, v, v0, pc

vars == << u, v, v0, pc >>

PCSet == {"Loop", "Swap", "Sub", "Done"}
VDomain == 1..VMax

GCD(a, b) ==
  LET S == 1..(a + b)
  IN CHOOSE g \in S:
       /\ \E k1 \in Nat: a = k1 * g
       /\ \E k2 \in Nat: b = k2 * g
       /\ \A e \in S:
            ((\E k3 \in Nat: a = k3 * e) /\ (\E k4 \in Nat: b = k4 * e)) => e <= g

Init ==
  /\ u = U0
  /\ v \in VDomain
  /\ v0 = v
  /\ pc = "Loop"

Loop ==
  /\ pc = "Loop"
  /\ IF u = 0
        THEN /\ pc' = "Done"
             /\ UNCHANGED <<u, v, v0>>
     ELSE IF u < v
        THEN /\ pc' = "Swap"
             /\ UNCHANGED <<u, v, v0>>
        ELSE /\ pc' = "Sub"
             /\ UNCHANGED <<u, v, v0>>

Swap ==
  /\ pc = "Swap"
  /\ u' = v
  /\ v' = u
  /\ v0' = v0
  /\ pc' = "Loop"

Sub ==
  /\ pc = "Sub"
  /\ u' = u - v
  /\ v' = v
  /\ v0' = v0
  /\ pc' = "Loop"

Done ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  \/ Loop
  \/ Swap
  \/ Sub
  \/ Done

Spec ==
  /\ Init
  /\ [][Next]_vars

TypeInv ==
  /\ u \in Nat
  /\ v \in VDomain
  /\ v0 \in VDomain
  /\ pc \in PCSet

GcdInvariant ==
  GCD(u, v) = GCD(U0, v0)

PostCondition ==
  (pc = "Done") => v = GCD(U0, v0)

Termination ==
  <> (pc = "Done")
=============================================================================