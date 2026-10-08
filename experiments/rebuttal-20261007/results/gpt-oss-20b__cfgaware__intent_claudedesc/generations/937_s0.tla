------------------------------ MODULE HourClock ------------------------------
Hours == 1 .. 12

VARIABLE hour

(* State predicate *)
Init == hour \in Hours

(* Tick action: advance hour by one with wrap‑around *)
Tick ==
  /\ hour' = IF hour = MAX(Hours) THEN MIN(Hours) ELSE hour + 1

Next == Tick

Spec == Init /\ [][Next]_<<hour>>
=============================================================================