---------------------------- MODULE PossibleCoverage ----------------------------
EXTENDS Naturals, TLC

VARIABLE x

vars == <<x>>

Init == x = 0

Next == x' = (x + 1) % 3

Spec == Init /\ [][Next]_vars

TypeOK == x \in Nat

-----------------------------------------------------------------------------
\* Predicates registered for possibility (coverage) tracking.

AllDone == x = 2

AtOne == x = 1

WrapAround == x = 2 /\ x' = 0

\* Names of the predicates tracked via the _POSSIBLE configuration directive.
_POSSIBLE == {"AllDone", "AtOne", "WrapAround"}

-----------------------------------------------------------------------------
\* Postcondition: each tracked predicate was witnessed exactly once.

PossibleCounts ==
    LET stats == TLCGet("all:named") IN
        /\ stats["AllDone"] = 1
        /\ stats["AtOne"] = 1
        /\ stats["WrapAround"] = 1

=============================================================================