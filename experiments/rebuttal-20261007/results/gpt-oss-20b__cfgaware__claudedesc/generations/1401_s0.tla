------------------------------ MODULE Github725b ------------------------------
EXTENDS Naturals, Temporal

VARIABLE outerX

\* Inner module
MODULE Inner725b
  VARIABLE x

  Init == x = 0

  Step ==
    /\ x < 3
    /\ x' = x + 1

  Fairness == WF_Enabled(x, Step)
END MODULE

\* Instantiate inner module as Svc with substitution outerX for x
MODULE Svc == Inner725b

Init == /\ outerX = 0
        /\ Svc.Init
        /\ outerX = Svc.x

Next ==
  \/ \* inner step
     /\ Svc.Step
     /\ outerX' = Svc.x'
  \/ \* stutter when not enabled
     /\ ~Enabled(Svc.Step)
     /\ UNCHANGED <<outerX, Svc.x>>

Fairness == WF_Enabled(outerX, Svc.Step)

Spec == Init /\ [][Next]_<<outerX, Svc.x>> /\ Fairness

Prop == <> (outerX = 3)

=============================================================================