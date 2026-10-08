MODULE CounterLoop
EXTENDS Naturals, TLC

CONSTANT B

VARIABLES c, pState

Run == "run"
Terminated == "term"

Init ==
  /\ c = 0
  /\ pState = Run

Increment ==
  /\ pState = Run
  /\ c < B
  /\ c' = c + 1
  /\ pState' = Run

Terminate ==
  /\ pState = Run
  /\ c = B
  /\ pState' = Terminated
  /\ c' = c

Stutter ==
  /\ pState = Terminated
  /\ pState' = Terminated
  /\ c' = c

Next == Increment \/ Terminate \/ Stutter

Spec == Init /\ [][Next]_<<c, pState>> /\ WF_Increment

SafetyInvariant == [] (c <= B)

NeverDecrease == [] (Next => c' >= c)

ProgressProperty == <> (pState = Terminated)

Liveness5 == <> (c = 5)

Liveness9to10 == <> (c = 9 /\ Increment)