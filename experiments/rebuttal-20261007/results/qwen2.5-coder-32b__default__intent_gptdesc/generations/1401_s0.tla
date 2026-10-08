------------------------------- MODULE TwoComponentSystem -------------------------------
EXTENDS Naturals, TLC

CONSTANTS MaxCount

VARIABLES counter

Init == counter = 0

SubcomponentEnabled == counter < MaxCount

Next ==
    \/ /\ SubcomponentEnabled
       /\ counter' = counter + 1
    \/ /\ ~SubcomponentEnabled
       /\ counter' = counter

Spec ==
    /\ Init
    /\ [][Next]_<<counter>>
    /\ WF_[SubcomponentEnabled]_<<counter>>

Liveness == <>(counter = MaxCount)

Safety ==
    /\ \A s, s' \in States : s' \in Next(s) => \/ counter'[s'] = counter[s'] + 1
                                                   \/ counter'[s'] = counter[s']

THEOREM Spec => []Safety

THEOREM Spec => Liveness
=====================================================================================