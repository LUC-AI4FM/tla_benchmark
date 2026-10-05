------------------------------ MODULE Paxos ------------------------------

CONSTANTS Ballot, Value, Acceptor, Quorum

VARIABLES messages, maxBallot, maxVBallot, maxValue, decision

vars == <<messages, maxBallot, maxVBallot, maxValue, decision>>

-----------------------------------------------------------------------------

Messages ==
    [type : {"1a"}, bal : Ballot]
    \cup
    [type : {"1b"}, bal : Ballot, acc : Acceptor, mbal : Ballot \cup {-1}, mval : Value \cup {None}]
    \cup
    [type : {"2a"}, bal : Ballot, val : Value]
    \cup
    [type : {"2b"}, bal : Ballot, acc : Acceptor, val : Value]

None == CHOOSE v : v \notin Value

PaxosTypeOK ==
    /\ messages \subseteq Messages
    /\ maxBallot \in [Acceptor -> Ballot \cup {0}]
    /\ maxVBallot \in [Acceptor -> Ballot \cup {-1}]
    /\ maxValue \in [Acceptor -> Value \cup {None}]
    /\ decision \in Value \cup {None}

-----------------------------------------------------------------------------

Init ==
    /\ messages = {}
    /\ maxBallot = [a \in Acceptor |-> 0]
    /\ maxVBallot = [a \in Acceptor |-> -1]
    /\ maxValue = [a \in Acceptor |-> None]
    /\ decision = None

-----------------------------------------------------------------------------

Send(m) == messages' = messages \cup {m}

PaxosPrepare(b) ==
    /\ b # 0
    /\ Send([type |-> "1a", bal |-> b])
    /\ UNCHANGED <<maxBallot, maxVBallot, maxValue, decision>>

PaxosPromise(a, m) ==
    /\ m \in messages
    /\ m.type = "1a"
    /\ m.bal > maxBallot[a]
    /\ maxBallot' = [maxBallot EXCEPT ![a] = m.bal]
    /\ Send([type |-> "1b", bal |-> m.bal, acc |-> a, 
             mbal |-> maxVBallot[a], mval |-> maxValue[a]])
    /\ UNCHANGED <<maxVBallot, maxValue, decision>>

ForcedValue(Q, b) ==
    LET msgs1b == {m \in messages : m.type = "1b" /\ m.bal = b /\ m.acc \in Q}
        accepted == {m \in msgs1b : m.mbal # -1}
    IN IF accepted = {} 
       THEN None
       ELSE (CHOOSE m \in accepted : \A m2 \in accepted : m.mbal >= m2.mbal).mval

PaxosAccept(b, v) ==
    /\ b # 0
    /\ \E Q \in Quorum :
        /\ \A a \in Q : \E m \in messages : m.type = "1b" /\ m.bal = b /\ m.acc = a
        /\ LET forced == ForcedValue(Q, b)
           IN IF forced = None 
              THEN v \in Value
              ELSE v = forced
    /\ ~\E m \in messages : m.type = "2a" /\ m.bal = b
    /\ Send([type |-> "2a", bal |-> b, val |-> v])
    /\ UNCHANGED <<maxBallot, maxVBallot, maxValue, decision>>

PaxosAccepted(a, m) ==
    /\ m \in messages
    /\ m.type = "2a"
    /\ m.bal >= maxBallot[a]
    /\ maxBallot' = [maxBallot EXCEPT ![a] = m.bal]
    /\ maxVBallot' = [maxVBallot EXCEPT ![a] = m.bal]
    /\ maxValue' = [maxValue EXCEPT ![a] = m.val]
    /\ Send([type |-> "2b", bal |-> m.bal, acc |-> a, val |-> m.val])
    /\ UNCHANGED decision

PaxosDecide ==
    /\ decision = None
    /\ \E b \in Ballot, v \in Value, Q \in Quorum :
        \A a \in Q : \E m \in messages : 
            m.type = "2b" /\ m.bal = b /\ m.acc = a /\ m.val = v
    /\ decision' = CHOOSE v \in Value : 
        \E b \in Ballot, Q \in Quorum :
            \A a \in Q : \E m \in messages : 
                m.type = "2b" /\ m.bal = b /\ m.acc = a /\ m.val = v
    /\ UNCHANGED <<messages, maxBallot, maxVBallot, maxValue>>

-----------------------------------------------------------------------------

Next ==
    \/ \E b \in Ballot : PaxosPrepare(b)
    \/ \E a \in Acceptor, m \in messages : PaxosPromise(a, m)
    \/ \E b \in Ballot, v \in Value : PaxosAccept(b, v)
    \/ \E a \in Acceptor, m \in messages : PaxosAccepted(a, m)
    \/ PaxosDecide

Fairness == SF_vars(PaxosDecide)

PaxosSpec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

ProposedValues ==
    {m.val : m \in {msg \in messages : msg.type = "2a"}}

PaxosNontriviality ==
    decision # None => decision \in ProposedValues

PaxosConsistency ==
    [][decision # None => decision' = decision]_vars

Liveness == FALSE

=============================================================================