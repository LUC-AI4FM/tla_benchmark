------------------------------- MODULE ConstantTrue -------------------------------

VARIABLES b

Init ==
  b = TRUE

Next ==
  UNCHANGED b

Spec ==
  Init /\ [][Next]_<<b>>

Inv ==
  b = TRUE

Live ==
  [](ENABLED Next)

Prop ==
  []Inv /\ Live

===============================================================================