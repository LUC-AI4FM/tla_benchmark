MODULE TinyClock

EXTENDS Naturals, TLC

VARIABLE clock

IsBool(x) == x \in BOOLEAN

Check(b, n) ==
  IF n = 0 THEN FALSE
  ELSE IF b THEN TRUE
       ELSE Check(b, n-1)

Flip(b, n) ==
  IF n = 0 THEN TRUE
  ELSE NOT Check(b, n-1)

Init ==
  /\ clock = FALSE \/ Check(clock, 3)
  (* TLC coverage: recursive operator call appears in Init; covered by TLC's support for recursion *)

Next ==
  /\ clock' = NOT clock

TypeInvariant == IsBool(clock)

Spec == Init /\ [][Next]_<<clock>>

Safety == TypeInvariant

===============================================================================