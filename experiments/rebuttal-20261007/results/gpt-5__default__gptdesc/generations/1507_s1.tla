----------------------------- MODULE TinyClock -----------------------------

EXTENDS TLC

VARIABLES clock

RECURSIVE Check(_)
RECURSIVE Flip(_)

Check(b) ==
  IF b \in BOOLEAN THEN TRUE ELSE Check(TRUE)

Flip(b) ==
  IF b = TRUE THEN FALSE
  ELSE IF b = FALSE THEN TRUE
  ELSE Flip(TRUE)

TypeOK ==
  Check(clock)

Init ==
  /\ clock = Flip(TRUE)
  /\ TypeOK
  \* TLC note: Init contains a recursive operator call via Flip(TRUE),
  \* and TypeOK calls the recursive operator Check on the state variable.

Constraint ==
  /\ Check(clock)
  /\ clock = Flip(Flip(clock))

Next ==
  /\ clock' = Flip(clock)

Spec ==
  /\ Init
  /\ [][Next]_clock
  /\ []Constraint

============================================================================