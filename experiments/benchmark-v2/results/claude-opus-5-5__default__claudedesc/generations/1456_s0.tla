---------------------------- MODULE SubsetPrimed ----------------------------
EXTENDS Naturals, FiniteSets, TLC

VARIABLES x, y

vars == <<x, y>>

Init ==
    /\ x \subseteq {1, 2}
    /\ y = {1, 2, 3}

Next ==
    /\ y' = y
    /\ x' \subseteq y'

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants *)

TypeOK == x \subseteq {1, 2, 3}

Inv ==
    /\ ENABLED (x' \subseteq {1})
    /\ y = {1, 2, 3}

-----------------------------------------------------------------------------
(* Predicates tracked via TLC's _POSSIBLE directive *)

\* State predicate: every reachable state (8 in total) satisfies it.
FullSet == y = {1, 2, 3}

\* Transition predicate: x gains the element 3.
\* There are 4 states without 3 and 4 successors with 3, giving 16 transitions.
GainThree == (3 \notin x) /\ (3 \in x')

_POSSIBLE == <<FullSet, GainThree>>

-----------------------------------------------------------------------------
(* Postcondition: TLC found exactly 8 states satisfying FullSet and *)
(* exactly 16 transitions satisfying GainThree.                    *)

PossibleCounts ==
    LET counts == TLCGet("possible")
    IN  /\ counts[1] = 8
        /\ counts[2] = 16

=============================================================================