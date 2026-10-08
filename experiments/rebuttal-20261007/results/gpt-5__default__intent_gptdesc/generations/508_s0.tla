---- MODULE SingleStepProgram ----
EXTENDS Integers

CONSTANTS Interval
ASSUME Interval = 1..10

VARIABLES x, done

TypeOK == /\ x \in Interval
          /\ done \in BOOLEAN

BoundOk == x * x <= 100

Init == /\ x \in Interval
        /\ done = FALSE

Assert ==
  /\ ~done
  /\ x \in Interval
  /\ x * x <= 100
  /\ x' = x
  /\ done' = TRUE

TerminatedStutter ==
  /\ done
  /\ UNCHANGED <<x, done>>

Next == Assert \/ TerminatedStutter

Spec ==
  /\ Init
  /\ [][Next]_<<x, done>>
  /\ WF_<<x, done>>(Assert)

SafetyInv == /\ TypeOK
             /\ BoundOk

Termination == <>done

THEOREM Spec => []SafetyInv
THEOREM Spec => Termination
==============================