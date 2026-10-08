------------------------------- MODULE SubsetSystem -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Universe
VARIABLES subset

Init == /\ subset \subseteq Universe
        /\ subset /= Universe
        /\ Cardinality(Universe) = 3

Next == \/ /\ CHOOSE newSubset \in SUBSET Universe: newSubset /= subset
          \/ /\ CHOOSE element \in Universe \ subset: subset' = subset \cup {element}

Spec == /\ Init
        /\ [][Next]_<<subset>>
        /\ WF_next(<<subset>>)

Invariants ==
    /\ subset \subseteq Universe
    /\ Universe = {1, 2, 3}

FullSetReached == \E s \in States: s.subset = Universe

ElementGained(element) == \E <<s, s'>> \in StatePairs: element \notin s.subset /\ element \in s'.subset

=============================================================================