MODULE SimpleClock
EXTENDS Naturals

VARIABLE hr

(* Predicate for initial hour *)
HCini == 1 <= hr /\ hr <= 12

(* Next state action *)
HCnxt ==
    hr' = IF hr = 12 THEN 1 ELSE hr + 1

Init == HCini

Next == HCnxt

Spec == Init /\ [][Next]_hr

THEOREM HCiniAlways == Spec => []HCini
PROOF
  OBVIOUS
QED