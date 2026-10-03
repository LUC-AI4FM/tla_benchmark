------------------------------ MODULE OneVar ------------------------------
EXTENDS Naturals

VARIABLE x

Init == 
  x = 0

Next ==
  \/ (x = 0 /\ x' \in {1,2})
  \/ (x #= 0 /\ x' = 0)

Spec == Init /\ [][Next]_x /\ WF_x(Next)

StabilizeAwayFrom12 == <>[] (x = 0)
InfReturnZero      == []<>(x = 0)
NotStabilizeAway   == ~StabilizeAwayFrom12

Post ==
  LET
    Trace == << [x: 0], [x: 1], [x: 0] >>
  IN
    /\ Trace[1].x = 0
    /\ Trace[2].x = 1
    /\ Trace[3].x = 0

=============================================================================