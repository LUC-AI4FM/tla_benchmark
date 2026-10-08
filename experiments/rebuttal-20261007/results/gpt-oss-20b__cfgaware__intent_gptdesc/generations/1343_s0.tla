```tla
---- MODULE SimpleConcurrentSystem ----
EXTENDS Naturals, TLC

VARIABLES loc1, loc2

(* The vector of all variables used in the temporal operator *)
vars == <<loc1, loc2>>

Init ==
  /\ loc1 = 0
  /\ loc2 = 0
  /\ loc1 = loc2

Next ==
  /\ loc1' = loc1
  /\ loc2' = loc2

Spec == Init /\ [][Next]_vars

(* The set of all states that can be reached from the initial state *)
StateSpace == {<<0,0>>}

EqInvariant == (loc1 = loc2)

Safety == [] EqInvariant

NoChangeProperty == Init /\ [](Next)
```