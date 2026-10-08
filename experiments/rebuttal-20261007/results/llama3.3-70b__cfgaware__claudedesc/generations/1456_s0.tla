---------------------------- MODULE SubsetConstraintTest ----------------------------
EXTENDS Integers

CONSTANT None

VARIABLE x, y

Init == (* Initial condition *)
        /\ x \subseteq {1, 2}
        /\ y = {1, 2, 3}

Next == (* Next-state relation *)
        /\ y' = y
        /\ x' \subseteq y'

TypeOK == (* Type invariant: x is a subset of {1, 2, 3} *)
         x \subseteq {1, 2, 3}

Inv == (* Invariant: Action enabling and y equals {1, 2, 3} *)
      /\ <>(x' \subseteq {1})
      /\ y = {1, 2, 3}

FullSet == (* State predicate: x is the full set {1, 2, 3} *)
          x = {1, 2, 3}

GainThree == (* Transition predicate: x gains element 3 *)
             3 \in x' /\ 3 \notin x

PossibleCounts == (* Postcondition: TLC found correct number of states and transitions *)
                  /\ [_POSSIBLE FullSet]_states = 8
                  /\ [_POSSIBLE GainThree]_transitions = 16

=============================================================================