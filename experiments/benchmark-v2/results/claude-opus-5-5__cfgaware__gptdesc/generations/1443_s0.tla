---------------------------- MODULE PossibleCoverage ----------------------------
EXTENDS Naturals, TLC

VARIABLE x

vars == <<x>>

Init == x = 0

Next == x' = (x + 1) % 3

Spec == Init /\ [][Next]_vars

\* Helper predicates
AtOne == x = 1

AllDone == x = 2

WrapAround == x = 2 /\ x' = 0

\* Names of the predicates whose coverage is tracked
_POSSIBLE == <<"AtOne", "AllDone", "WrapAround">>

\* TLC-specific check: each named predicate is counted exactly once
PossibleCounts ==
    LET counts == TLCGet("possible")
    IN  /\ counts["AtOne"] = 1
        /\ counts["AllDone"] = 1
        /\ counts["WrapAround"] = 1

=============================================================================