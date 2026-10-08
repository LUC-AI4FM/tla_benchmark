---------------------------- MODULE FastPaxos ----------------------------

EXTENDS Integers, FiniteSets

CONSTANTS Replicas, Values, Ballots, FastBallots, ClassicQuorums, FastQuorums

VARIABLES msgs, maxBal, maxVBal, maxVal, decision, cValue

vars == <<msgs, maxBal, maxVBal, maxVal, decision, cValue>>

Acceptors == Replicas

Any == CHOOSE v : v \notin Values

Messages ==
    [type : {"P2a"}, bal : Ballots, val : Values \cup {Any}]
    \cup
    [type : {"P2b"}, bal : Ballots, acc : Acceptors, val : Values]
    \cup
    [type : {"Decision"}, val : Values]

FastTypeOK ==
    /\ msgs \subseteq Messages
    /\ maxBal \in [Acceptors -> Ballots \cup {0}]
    /\ maxVBal \in [Acceptors -> Ballots \cup {0}]
    /\ maxVal \in [Acceptors -> Values \cup {Any}]
    /\ decision \subseteq Values
    /\ cValue \in Values \cup {Any}

FastInit ==
    /\ msgs = {}
    /\ maxBal = [a \in Acceptors |-> 0]
    /\ maxVBal = [a \in Acceptors |-> 0]
    /\ maxVal = [a \in Acceptors |-> Any]
    /\ decision = {}
    /\ cValue = Any

IsFastBallot(b) == b \in FastBallots

Send(m) == msgs' = msgs \cup {m}

Phase2aFast(b) ==
    /\ IsFastBallot(b)
    /\ ~\E m \in msgs : m.type = "P2a" /\ m.bal = b
    /\ Send([type |-> "P2a", bal |-> b, val |-> Any])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, decision, cValue>>

Phase2aClassic(b, v) ==
    /\ ~IsFastBallot(b)
    /\ v \in Values
    /\ ~\E m \in msgs : m.type = "P2a" /\ m.bal = b
    /\ Send([type |-> "P2a", bal |-> b, val |-> v])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, decision, cValue>>

Phase2bFast(a, b, v) ==
    /\ IsFastBallot(b)
    /\ v \in Values
    /\ \E m \in msgs : m.type = "P2a" /\ m.bal = b /\ m.val = Any
    /\ b >= maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = b]
    /\ maxVBal' = [maxVBal EXCEPT ![a] = b]
    /\ maxVal' = [maxVal EXCEPT ![a] = v]
    /\ Send([type |-> "P2b", bal |-> b, acc |-> a, val |-> v])
    /\ UNCHANGED <<decision, cValue>>

Phase2bClassic(a, b) ==
    /\ ~IsFastBallot(b)
    /\ \E m \in msgs : m.type = "P2a" /\ m.bal = b /\ m.val \in Values
    /\ b >= maxBal[a]
    /\ LET m == CHOOSE m \in msgs : m.type = "P2a" /\ m.bal = b /\ m.val \in Values
       IN /\ maxBal' = [maxBal EXCEPT ![a] = b]
          /\ maxVBal' = [maxVBal EXCEPT ![a] = b]
          /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
          /\ Send([type |-> "P2b", bal |-> b, acc |-> a, val |-> m.val])
    /\ UNCHANGED <<decision, cValue>>

P2bMsgsForBallot(b) == {m \in msgs : m.type = "P2b" /\ m.bal = b}

ValuesInP2b(b) == {m.val : m \in P2bMsgsForBallot(b)}

AccsInP2bForVal(b, v) == {m.acc : m \in {m \in P2bMsgsForBallot(b) : m.val = v}}

FastDecide(b, v) ==
    /\ IsFastBallot(b)
    /\ v \in Values
    /\ \E Q \in FastQuorums :
        /\ \A a \in Q : \E m \in msgs : m.type = "P2b" /\ m.bal = b /\ m.acc = a /\ m.val = v
    /\ decision' = decision \cup {v}
    /\ Send([type |-> "Decision", val |-> v])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, cValue>>

ClassicDecide(b, v) ==
    /\ ~IsFastBallot(b)
    /\ v \in Values
    /\ \E Q \in ClassicQuorums :
        /\ \A a \in Q : \E m \in msgs : m.type = "P2b" /\ m.bal = b /\ m.acc = a /\ m.val = v
    /\ decision' = decision \cup {v}
    /\ Send([type |-> "Decision", val |-> v])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, cValue>>

CollisionRecovery(fastBal, classicBal) ==
    /\ IsFastBallot(fastBal)
    /\ ~IsFastBallot(classicBal)
    /\ classicBal > fastBal
    /\ \E FQ \in FastQuorums :
        LET p2bs == {m \in msgs : m.type = "P2b" /\ m.bal = fastBal /\ m.acc \in FQ}
            accs == {m.acc : m \in p2bs}
            vals == {m.val : m \in p2bs}
        IN /\ accs = FQ
           /\ Cardinality(vals) > 1
           /\ LET majority == Cardinality(FQ) \div 2 + 1
                  majVals == {v \in vals : Cardinality({m \in p2bs : m.val = v}) >= majority}
                  chosenVal == IF majVals # {}
                               THEN CHOOSE v \in majVals : TRUE
                               ELSE CHOOSE v \in vals : TRUE
              IN /\ cValue' = chosenVal
                 /\ Send([type |-> "P2a", bal |-> classicBal, val |-> chosenVal])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, decision>>

FastNext ==
    \/ \E b \in Ballots : Phase2aFast(b)
    \/ \E b \in Ballots, v \in Values : Phase2aClassic(b, v)
    \/ \E a \in Acceptors, b \in Ballots, v \in Values : Phase2bFast(a, b, v)
    \/ \E a \in Acceptors, b \in Ballots : Phase2bClassic(a, b)
    \/ \E b \in Ballots, v \in Values : FastDecide(b, v)
    \/ \E b \in Ballots, v \in Values : ClassicDecide(b, v)
    \/ \E fb, cb \in Ballots : CollisionRecovery(fb, cb)

FastDecideEnabled == \E b \in Ballots, v \in Values : FastDecide(b, v)
ClassicDecideEnabled == \E b \in Ballots, v \in Values : ClassicDecide(b, v)

FastSpec ==
    /\ FastInit
    /\ [][FastNext]_vars
    /\ SF_vars(FastDecideEnabled /\ \E b \in Ballots, v \in Values : FastDecide(b, v))
    /\ SF_vars(ClassicDecideEnabled /\ \E b \in Ballots, v \in Values : ClassicDecide(b, v))

ProposedValues == {m.val : m \in {m \in msgs : m.type = "P2b" /\ m.val \in Values}}

FastNontriviality == decision \subseteq ProposedValues

PaxosConsistency == Cardinality(decision) <= 1

=============================================================================