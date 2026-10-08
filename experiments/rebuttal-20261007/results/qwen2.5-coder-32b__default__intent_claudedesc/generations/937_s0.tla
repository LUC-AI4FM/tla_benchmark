------------------------------- MODULE SimpleClock -------------------------------

EXTENDS HourClock

CONSTANTS Tick

VARIABLES hour

Init == hour = 1

Next ==
    \/ /\ Tick \in UNCHANGED <<hour>>
       /\ hour' = (hour + 1) % 12
          \/ hour' = 12
    \/ /\ NOT Tick \in UNCHANGED <<hour>>

Spec ==
    Init /\ [][Next]_<<Tick>>

WF_Tick == WF_[Tick]_<<Tick>>

THEOREM Spec => WF_Tick

THEOREM Spec => <>[] (hour \in 1..12)

THEOREM Spec => <>(hour = 1) /\ <>(hour = 2) /\ <>(hour = 3) /\ <>(hour = 4) /\ <>(hour = 5) /\ <>(hour = 6) /\ <>(hour = 7) /\ <>(hour = 8) /\ <>(hour = 9) /\ <>(hour = 10) /\ <>(hour = 11) /\ <>(hour = 12)

=============================================================================