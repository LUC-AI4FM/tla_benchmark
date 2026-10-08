---------------------------- MODULE OneStepConsensus ----------------------------

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, F, T \* Number of processes, number of faulty processes, threshold

VARIABLES sentMsgs, recvMsgs, faulty, states

Init == /\ sentMsgs = <<0>> ^ N
        /\ recvMsgs = [p \in 1..N -> {}]
        /\ faulty = {}
        /\ states = [p \in 1..N -> "idle"]

Next ==
    \/ \/ \E p \in 1..N - faulty : /\ states[p] = "idle"
                                   /\ sentMsgs' = <<v \in 1..N -> IF v = p THEN CHOOSE val \in {0, 1} ELSE sentMsgs[v]>>
                                   /\ recvMsgs' = [recvMsgs EXCEPT ![p] = {}]
                                   /\ faulty' = faulty
                                   /\ states' = [states EXCEPT ![p] = "sent"]
       \/ \/ \E p \in 1..N - faulty : /\ states[p] = "sent"
                                   /\ recvMsgs' = [recvMsgs EXCEPT ![p] = {v \in sentMsgs}]
                                   /\ faulty' = faulty
                                   /\ states' = [states EXCEPT ![p] = "received"]
       \/ \/ \E p \in 1..N - faulty : /\ states[p] = "received"
                                   /\ LET voteCount[m \in {0, 1}] == Cardinality({v \in recvMsgs[p] : v = m}) IN
                                   /\ IF voteCount[0] >= T \/ voteCount[1] >= T THEN states' = [states EXCEPT ![p] = "decided"]
                                                                 ELSE states' = states
                                   /\ sentMsgs' = sentMsgs
                                   /\ recvMsgs' = recvMsgs
                                   /\ faulty' = faulty
       \/ \/ \E p \in 1..N - faulty : /\ states[p] = "idle"
                                   /\ faulty' = faulty \cup {p}
                                   /\ states' = [states EXCEPT ![p] = "faulty"]
                                   /\ sentMsgs' = sentMsgs
                                   /\ recvMsgs' = recvMsgs

Spec ==
    /\ Init
    /\ [][Next]_<<sentMsgs, recvMsgs, faulty, states>>
    /\ WF_[Next]_<<sentMsgs, recvMsgs, faulty, states>>

\* Safety Properties
Safety == \/ \A p \in 1..N : states[p] = "decided" => \E m \in {0, 1} : Cardinality({v \in recvMsgs[p] : v = m}) >= T

\* Liveness Properties
Liveness == \/ \A p \in 1..N - faulty : <>(states[p] = "decided")

=============================================================================