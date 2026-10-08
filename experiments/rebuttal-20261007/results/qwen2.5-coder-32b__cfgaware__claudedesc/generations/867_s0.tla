------------------------------- MODULE PaxosSpec -------------------------------

CONSTANTS Replicas, Ballots, Values

VARIABLES messages, maxBallot, maxVBallot, maxValue, decision

(* --algorithm Paxos
variables 
    messages = {},
    maxBallot = [r \in Replicas |-> 0],
    maxVBallot = [r \in Replicas |-> 0],
    maxValue = [r \in Replicas |-> <<>>],
    decision = <<>>
end algorithm *)

PaxosTypeOK == 
    /\ messages \subseteq (Replicas \X Ballots \X Values)
    /\ maxBallot \in [Replicas -> Ballots]
    /\ maxVBallot \in [Replicas -> Ballots]
    /\ maxValue \in [Replicas -> Values]
    /\ decision \in Values \/ decision = <<>>

PaxosPrepare ==
    \E r \in Replicas, b \in Ballots \ {0} :
        /\ b > maxBallot[r]
        /\ messages' = messages \cup {[r, b, v] : v \in Values}
        /\ UNCHANGED <<maxBallot, maxVBallot, maxValue, decision>>

PaxosPromise ==
    \E r1, r2 \in Replicas, b1, b2 \in Ballots :
        /\ [r1, b1, _] \in messages
        /\ b1 > maxBallot[r2]
        /\ messages' = messages \cup {[r2, b1, <<maxVBallot[r2], maxValue[r2]>>]}
        /\ maxBallot' = [maxBallot EXCEPT ![r2] = b1]
        /\ UNCHANGED <<maxVBallot, maxValue, decision>>

PaxosAccept ==
    \E r \in Replicas, b \in Ballots :
        /\ LET quorumMsgs == {m \in messages : m[2] = b}
           quorumSize == Cardinality({r' \in Replicas : \E m \in quorumMsgs (m[1] = r')})
        IN
        /\ quorumSize >= 3
        /\ LET ForcedValue == CHOOSE v \in Values : \A m \in quorumMsgs (v = m[3][2])
           chosenValue == IF \E v \in Values : (\A m \in quorumMsgs (m[3][2] = v)) THEN ForcedValue ELSE CHOOSE v \in Values
        IN
        /\ messages' = messages \cup {[r, b, chosenValue]}
        /\ UNCHANGED <<maxBallot, maxVBallot, maxValue, decision>>

PaxosAccepted ==
    \E r1, r2 \in Replicas, b \in Ballots, v \in Values :
        /\ [r1, b, _] \in messages
        /\ b >= maxBallot[r2]
        /\ messages' = messages \cup {[r2, b, v]}
        /\ maxBallot' = [maxBallot EXCEPT ![r2] = b]
        /\ maxVBallot' = [maxVBallot EXCEPT ![r2] = b]
        /\ maxValue' = [maxValue EXCEPT ![r2] = v]
        /\ UNCHANGED decision

PaxosDecide ==
    \E r \in Replicas, b \in Ballots, v \in Values :
        /\ LET quorumMsgs == {m \in messages : m[1] = r /\ m[2] = b /\ m[3] = v}
           quorumSize == Cardinality(quorumMsgs)
        IN
        /\ quorumSize >= 3
        /\ decision' = v
        /\ UNCHANGED <<messages, maxBallot, maxVBallot, maxValue>>

PaxosNontriviality ==
    \A r \in Replicas, b \in Ballots, v \in Values :
        /\ [r, b, v] \in messages
        => v \in {mv : mv \in Values /\ \E m \in messages (m[3] = mv)}

PaxosConsistency ==
    \/ decision = <<>>
    \/ \A r \in Replicas, b \in Ballots, v \in Values :
        /\ [r, b, v] \in messages
        => v = decision

Next == PaxosPrepare \/ PaxosPromise \/ PaxosAccept \/ PaxosAccepted \/ PaxosDecide

Spec ==
    /\ Init
    /\ [][Next]_<<messages, maxBallot, maxVBallot, maxValue, decision>>
    /\ WF_[PaxosDecide]_<<messages, maxBallot, maxVBallot, maxValue, decision>>

Init == 
    /\ messages = {}
    /\ maxBallot \in [Replicas -> {0}]
    /\ maxVBallot \in [Replicas -> {0}]
    /\ maxValue \in [Replicas -> {<<>>}]
    /\ decision = <<>>

THEOREM Spec => []PaxosTypeOK
THEOREM Spec => []PaxosNontriviality
THEOREM Spec => []PaxosConsistency

LIVENESS == FALSE

=============================================================================