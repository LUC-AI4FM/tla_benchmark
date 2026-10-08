---------------------------- MODULE Clock --------------------------------
EXTENDS Integers

CONSTANT HC, HC2

VARIABLE hr

Init == (hr \in 1..12)

Next == hr' = IF hr = 12 THEN 1 ELSE hr + 1

Next2 == hr' = (hr mod 12) + 1

Spec == Init /\ [][Next]_hr

Spec2 == Init /\ [][Next2]_hr

THEOREM Spec => []Inv
PROOF
  Inv == hr \in 1..12
  OBVIOUS
THEOREM

THEOREM Spec => <>[]<<hr' = Next>>_hr
PROOF
  <<hr' = Next>> == <><<hr' = IF hr = 12 THEN 1 ELSE hr + 1>>_hr
  OBVIOUS
THEOREM

THEOREM Spec2 => []Inv
PROOF
  Inv == hr \in 1..12
  OBVIOUS
THEOREM

THEOREM Spec2 => <>[]<<hr' = Next2>>_hr
PROOF
  <<hr' = Next2>> == <><<hr' = (hr mod 12) + 1>>_hr
  OBVIOUS
THEOREM

HC == Spec
HC2 == Spec2
=============================================================================