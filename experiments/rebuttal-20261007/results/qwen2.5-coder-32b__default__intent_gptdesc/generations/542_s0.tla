------------------------------- MODULE TwoWorkersIncrement -------------------------------
EXTENDS Naturals, TLC

CONSTANTS Worker1, Worker2

VARIABLES counter, finished

Init == /\ counter = 0
        /\ finished = {}

Next ==
    \/ /\ Worker1 \notin finished
       /\ counter' = counter + 1
       /\ finished' = finished \cup {Worker1}
       /\ UNCHANGED <<finished - {Worker1}>>
    \/ /\ Worker2 \notin finished
       /\ counter' = counter + 1
       /\ finished' = finished \cup {Worker2}
       /\ UNCHANGED <<finished - {Worker2}>>
    \/ /\ finished = {Worker1, Worker2}
       /\ counter' = counter
       /\ finished' = finished

Spec ==
    /\ Init
    /\ [][Next]_<<counter, finished>>
    /\ WF_<<Worker1 \notin finished>>, Next>>_<<counter, finished>>
    /\ WF_<<Worker2 \notin finished>>, Next>>_<<counter, finished>>

Safety == 
    /\ counter \in Int
    /\ counter >= 0
    /\ \A s \in State: (s' \in State => counter' = counter + 1 \/ counter' = counter)
    /\ \A s \in State: (s' \in State => finished' = finished \cup {Worker1} \/ finished' = finished \cup {Worker2} \/ finished' = finished)

Liveness ==
    <>[](finished = {Worker1, Worker2})
    /\ <>(counter = 2)

State == <<counter, finished>>

=============================================================================