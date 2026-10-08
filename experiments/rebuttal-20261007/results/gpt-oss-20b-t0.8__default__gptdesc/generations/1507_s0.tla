----------------------------- MODULE TinyClock -----------------------------
EXTENDS Naturals, TLC

VARIABLE clock

(* Recursive operator definitions *)
Check(b) == b \in {TRUE, FALSE}

Flip(b) == IF b THEN FALSE ELSE TRUE

(* State predicates *)
ConstraintState == Check(Flip(clock))

Init ==
  /\ clock = FALSE
  /\ Check(clock)
  /\ ConstraintState

Next ==
  /\ clock' = Flip(clock)

Spec ==
  Init /\ [][Next]_<<clock>> /\ [] (Check(clock) /\ ConstraintState)

=============================================================================