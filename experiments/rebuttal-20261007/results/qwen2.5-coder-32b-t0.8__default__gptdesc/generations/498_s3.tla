------------------------------- MODULE MultiSlotConsensus ------------------------------

EXTENDS Integers, FiniteSets

CONSTANTS NumSlots

VARIABLES proposedValues, chosenValues

Init == 
  /\ proposedValues = {}
  /\ chosenValues = [s \in 1..NumSlots -> {}]

Next ==
  \/ /\ ELEM val \notin proposedValues
     /\ proposedValues' = proposedValues \cup {val}
     /\ UNCHANGED chosenValues
  \/ /\ EX \E s \in 1..NumSlots : chosenValues[s] = {}
     /\ \E val \in proposedValues : 
          /\ chosenValues' = [chosenValues EXCEPT ![s] = {val}]
          /\ UNCHANGED proposedValues

TypeOK ==
  /\ proposedValues \subseteq (UNION {v: TRUE})
  /\ chosenValues \in [1..NumSlots -> S]
  /\ \A s \in 1..NumSlots : chosenValues[s] \subseteq (UNION {v: TRUE}) /\ Cardinality(chosenValues[s]) <= 1

Nontrivial ==
  \/ proposedValues # {}
  \/ \E s \in 1..NumSlots : chosenValues[s] # {}

Stability ==
  \A val \in proposedValues, s \in 1..NumSlots :
    chosenValues[s] = {val} => UNCHANGED chosenValues[s]

PerSlotConsistency ==
  \A s1, s2 \in 1..NumSlots :
     /\ chosenValues[s1] # {}
     /\ chosenValues[s2] # {}
     => chosenValues[s1] = chosenValues[s2]

Spec ==
  Init /\ [][Next]_<<proposedValues, chosenValues>> /\ WF_next(<<proposedValues, chosenValues>>)

INVARS == TypeOK /\ Nontrivial /\ Stability /\ PerSlotConsistency

THEOREM Spec => []INVARS

LIVENESS ==
  \A s \in 1..NumSlots : 
    <>(Cardinality(chosenValues[s]) = 1)

WF_next(<<proposedValues, chosenValues>>) == WF_vars(proposedValues, chosenValues) /\ WFair(Next)

=============================================================================