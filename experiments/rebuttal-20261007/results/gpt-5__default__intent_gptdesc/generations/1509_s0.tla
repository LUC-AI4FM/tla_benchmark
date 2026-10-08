------------------------------ MODULE FiniteStateWithMap ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANT IDX

ASSUME
  /\ IsFiniteSet(IDX)
  /\ \E a \in IDX: \E b \in IDX: \E c \in IDX:
        a # b /\ b # c /\ a # c

ValSet == {1, 2, 3, 4, 5}

VARIABLES s, m

vars == << s, m >>

Init ==
  /\ s \in ValSet
  /\ m \in [IDX -> ValSet]
  /\ \E i \in IDX: m[i] = s

Next ==
  /\ s' \in ValSet
  /\ m' \in [IDX -> ValSet]
  /\ \E i \in IDX: m'[i] = s'

Spec == Init /\ [][Next]_vars

SafetyInv ==
  /\ s \in ValSet
  /\ m \in [IDX -> ValSet]
  /\ \E i \in IDX: m[i] = s

NoDeadlock == [] (ENABLED Next)

=============================================================================