------------------------------- MODULE FastPaxos -------------------------------
EXTENDS Paxos, FiniteSets

CONSTANTS Replicas, Values, Ballots, FastBallots, ClassicQuorums, FastQuorums

VARIABLES ballot, p2bMsgs, cValue, decided

Init == /\ ballot = <<>>
        /\ p2bMsgs = [r \in Replicas -> {}]
        /\ cValue = <<>>
        /\ decided = FALSE

Next ==
    \/ \/ /\ ballot' = <<Ballot>>
       /\ UNCHANGED <<p2bMsgs, cValue, decided>>
       \/ /\ ballot' = ballot
          /\ \/ /\ EXIST r \in Replicas : p2bMsgs[r]' = p2bMsgs[r] \cup {<<ballot[1], Value>>}
             /\ UNCHANGED <<cValue, decided>>
             \/ /\ FastQuorumAgrees(p2bMsgs)
                /\ cValue' = ChosenValue(ballot[1], p2bMsgs)
                /\ decided' = TRUE
                /\ UNCHANGED p2bMsgs
          \/ /\ ClassicQuorumAgrees(ballot[1], p2bMsgs)
             /\ decided' = TRUE
             /\ UNCHANGED <<cValue, p2bMsgs>>
    \/ /\ ballot' = ballot
       /\ cValue' = ChosenValue(ballot[1], p2bMsgs)
       /\ decided' = FALSE
       /\ UNCHANGED p2bMsgs

FastQuorumAgrees(p2bs) ==
    \E q \in FastQuorums : \A r \in q : \E v \in Values : p2bs[r] = {<<ballot[1], v>>}

ClassicQuorumAgrees(ballot, p2bs) ==
    \E q \in ClassicQuorums : \A r \in q : \E v \in Values : p2bs[r] = {<<ballot, v>>}

ChosenValue(ballot, p2bs) ==
    LET counts == [v \in Values |-> Cardinality({r \in Replicas : <<ballot, v>> \in p2bs[r]})]
    IN CHOOSE v \in Values : counts[v] = Max({counts[v] : v \in Values})

FastTypeOK ==
    /\ ballot \in Ballots
    /\ \A r \in Replicas : p2bMsgs[r] \subseteq {<<Ballot, Value>> : Ballot \in Ballots, Value \in Values}
    /\ cValue \in Values \/ cValue = <<>>
    /\ decided \in BOOLEAN

FastNontriviality ==
    \A v \in Values : (v \in {p2bMsgs[r][1][2] : r \in Replicas} => v \in Values)

PaxosConsistency ==
    \/ ~decided
    \/ \E v \in Values : \A w \in Values : (w = v <=> decidedValue(w))

Spec ==
    /\ Init
    /\ [][Next]_<<ballot, p2bMsgs, cValue, decided>>
    /\ WF_fastDecide(<<ballot, p2bMsgs, cValue, decided>>)
    /\ SF_classicDecide(<<ballot, p2bMsgs, cValue, decided>>)

fastDecide ==
    \E q \in FastQuorums : \A r \in q : \E v \in Values : <<ballot[1], v>> \in p2bMsgs[r]

classicDecide ==
    ClassicQuorumAgrees(ballot[1], p2bMsgs)

WF_fastDecide(vars) == WF_vars!(fastDecide, vars)
SF_classicDecide(vars) == SF_vars!(classicDecide, vars)

=============================================================================