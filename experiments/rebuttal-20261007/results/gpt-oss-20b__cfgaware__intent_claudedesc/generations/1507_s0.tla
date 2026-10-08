------------------------------ MODULE BoolClock ------------------------------
EXTENDS Naturals

VARIABLE clk

BOOLEAN == {TRUE, FALSE}

InitRec(n) ==
  IF n = 0 THEN
    clk = FALSE
  ELSE
    InitRec(n-1)

Init == InitRec(0)

NextRec(n) ==
  IF n = 0 THEN
    /\ clk' = NOT clk
  ELSE
    NextRec(n-1)

Next == NextRec(0)

TypeOKRec(n) ==
  IF n = 0 THEN
    clk \in BOOLEAN
  ELSE
    TypeOKRec(n-1)

TypeOK == TypeOKRec(0)

Spec == Init /\ [][Next]_<<clk>> /\ []TypeOK

=============================================================================