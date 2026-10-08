---------------------------- MODULE Spec ----------------------------

VARIABLE x

Init == x = 0

Next == UNCHANGED x

Spec == Init /\ [][Next]_x

AlwaysTrue == <>TRUE => <>[]TRUE

THEOREM AlwaysTrueTheorem == Spec => AlwaysTrue
PROOF
  <1>1. TRUE
    OBVIOUS
  <1>2. <>TRUE
    BY <1>1
  <1>3. []TRUE
    BY <1>1
  <1>4. <>[]TRUE
    BY <1>3
  <1>5. <>TRUE => <>[]TRUE
    BY <1>4
  <1> QED
    BY <1>5

=======================================================================