---------------------------- MODULE PaxosSpec ----------------------------

EXTENDS Integers, FiniteSets

CONSTANTS Acceptors, Proposers, Values, Ballots, Quorums

ASSUME QuorumAssumption == 
    /\ Quorums \subseteq SUBSET Acceptors
    /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 /= {}

ASSUME BallotAssumption == 
    /\ Ballots \subseteq Nat
    /\ Ballots /= {}

ASSUME ValueAssumption == Values /= {}

ASSUME AcceptorAssumption == Acceptors /= {}

ASSUME ProposerAssumption == Proposers /= {}

None == CHOOSE v : v \notin Values

VARIABLES
    maxBal,
    maxVBal,
    maxVal,
    msgs,
    proposed,
    decided

vars == <<maxBal, maxVBal, maxVal, msgs, proposed, decided>>

Message ==
    [type : {"prepare"}, bal : Ballots, proposer : Proposers]
    \cup
    [type : {"promise"}, bal : Ballots, acc : Acceptors, 
     maxVBal : Ballots \cup {-1}, maxVal : Values \cup {None}]
    \cup
    [type : {"accept"}, bal : Ballots, val : Values, proposer : Proposers]
    \cup
    [type : {"accepted"}, bal : Ballots, val : Values, acc : Acceptors]

PaxosTypeOK ==
    /\ maxBal \in [Acceptors -> Ballots \cup {-1}]
    /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
    /\ maxVal \in [Acceptors -> Values \cup {None}]
    /\ msgs \subseteq Message
    /\ proposed \subseteq Values
    /\ decided \subseteq Values

Init ==
    /\ maxBal = [a \in Acceptors |-> -1]
    /\ maxVBal = [a \in Acceptors |-> -1]
    /\ maxVal = [a \in Acceptors |-> None]
    /\ msgs = {}
    /\ proposed = {}
    /\ decided = {}

Send(m) == msgs' = msgs \cup {m}

Prepare(p, b) ==
    /\ ~\E m \in msgs : m.type = "prepare" /\ m.bal = b
    /\ Send([type |-> "prepare", bal |-> b, proposer |-> p])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, proposed, decided>>

Promise(a, b) ==
    /\ \E m \in msgs : m.type = "prepare" /\ m.bal = b
    /\ b > maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = b]
    /\ Send([type |-> "promise", bal |-> b, acc |-> a,
             maxVBal |-> maxVBal[a], maxVal |-> maxVal[a]])
    /\ UNCHANGED <<maxVBal, maxVal, proposed, decided>>

HighestAcceptedValue(Q, b) ==
    LET validPromises == {m \in msgs : m.type = "promise" /\ m.bal = b /\ m.acc \in Q}
        acceptedPromises == {m \in validPromises : m.maxVBal /= -1}
    IN IF acceptedPromises = {}
       THEN None
       ELSE LET maxAccBal == CHOOSE mb \in {m.maxVBal : m \in acceptedPromises} :
                               \A m \in acceptedPromises : m.maxVBal <= mb
                maxMsg == CHOOSE m \in acceptedPromises : m.maxVBal = maxAccBal
            IN maxMsg.maxVal

Accept(p, b, v) ==
    /\ \E Q \in Quorums :
        /\ \A a \in Q : \E m \in msgs : m.type = "promise" /\ m.bal = b /\ m.acc = a
        /\ LET hv == HighestAcceptedValue(Q, b)
           IN IF hv = None
              THEN v \in Values
              ELSE v = hv
    /\ proposed' = proposed \cup {v}
    /\ Send([type |-> "accept", bal |-> b, val |-> v, proposer |-> p])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, decided>>

Accepted(a, b, v) ==
    /\ \E m \in msgs : m.type = "accept" /\ m.bal = b /\ m.val = v
    /\ b >= maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = b]
    /\ maxVBal' = [maxVBal EXCEPT ![a] = b]
    /\ maxVal' = [maxVal EXCEPT ![a] = v]
    /\ Send([type |-> "accepted", bal |-> b, val |-> v, acc |-> a])
    /\ UNCHANGED <<proposed, decided>>

Decide(v) ==
    /\ \E Q \in Quorums :
        \E b \in Ballots :
            \A a \in Q : \E m \in msgs : m.type = "accepted" /\ m.bal = b /\ m.val = v /\ m.acc = a
    /\ decided' = decided \cup {v}
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, msgs, proposed>>

ProposerAction ==
    \E p \in Proposers :
        \E b \in Ballots :
            \/ Prepare(p, b)
            \/ \E v \in Values : Accept(p, b, v)

AcceptorAction ==
    \E a \in Acceptors :
        \E b \in Ballots :
            \/ Promise(a, b)
            \/ \E v \in Values : Accepted(a, b, v)

DecideAction ==
    \E v \in Values : Decide(v)

Next ==
    \/ ProposerAction
    \/ AcceptorAction
    \/ DecideAction

Spec == Init /\ [][Next]_vars

PaxosConsistency ==
    Cardinality(decided) <= 1

PaxosNontriviality ==
    \A v \in decided : v \in proposed

AcceptorMonotonicity ==
    /\ \A a \in Acceptors : maxVBal[a] <= maxBal[a]
    /\ \A a \in Acceptors : (maxVBal[a] = -1) <=> (maxVal[a] = None)

QuorumIntersection ==
    \A Q1, Q2 \in Quorums : Q1 \cap Q2 /= {}

MessageInvariant ==
    \A m \in msgs :
        /\ m.type = "promise" => 
            /\ (m.maxVBal = -1 <=> m.maxVal = None)
            /\ m.maxVBal < m.bal
        /\ m.type = "accepted" => m.val \in Values

SafetyInvariant ==
    /\ PaxosTypeOK
    /\ PaxosConsistency
    /\ PaxosNontriviality
    /\ AcceptorMonotonicity
    /\ QuorumIntersection
    /\ MessageInvariant

=============================================================================