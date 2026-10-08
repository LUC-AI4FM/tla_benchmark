------------------------------- MODULE SubsetSpec -------------------------------
EXTENDS FiniteSets

CONSTANTS U \* U = {1, 2, 3}
VARIABLES S, T

Init == /\ S \subseteq {1, 2}
        /\ T = U

Next == /\ T' = T
        /\ S' \subseteq T

Spec == Init /\ [][Next]_<<S>>

Inv1 == S \subseteq U
Inv2 == ENABLED (/\ S' = {1} \/ S' = {2} \/ S' = {3})

TypeOK == /\ S \in SUBSET U
         /\ T = U

Invariants == Inv1 /\ Inv2

SpecWithInvariants == Spec /\ WF_next(S)

POSSIBLE_FULL_SET == /\ S = U
NEW_ELEMENT_GAINED(s, s') == s' = s \cup {e} \* for some e \notin s

SpecWithPossibility ==
  LET fullSetCount == Cardinality({s \in SUBSET U : s = U})
      newElementCount == Cardinality({<<s, s'>> \in (SUBSET U) \X (SUBSET U) :
                                      s \subset s' /\ s' \subseteq U})
  IN
    SpecWithInvariants
    /\ <>(POSSIBLE fullSetCount : POSSIBLE_FULL_SET)
    /\ <>(POSSIBLE newElementCount : \E e \in U : NEW_ELEMENT_GAINED(S, S'))

THEOREM SpecWithPossibility

=============================================================================