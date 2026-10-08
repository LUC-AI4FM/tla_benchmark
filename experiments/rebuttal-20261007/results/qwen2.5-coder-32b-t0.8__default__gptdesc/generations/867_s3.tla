------------------------------ MODULE Paxos ------------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Proposers, Acceptors, Values

VARIABLES sentMessages, decision, acceptorState

(* --algorithm paxos
variables 
    sentMessages = {},  \* Set of all messages sent: { <<sender, receiver, type, ballot, value>>, ... }
    decision = "",     \* Representative decision value
    acceptorState = [a \in Acceptors |> [highestBallotSeen |>> 0, highestBallotAccepted |>> 0, acceptedValue |>> ""]]  \* State of each acceptor

Init == 
    /\ sentMessages = {}
    /\ decision = ""
    /\ (\A a \in Acceptors: acceptorState[a] = [highestBallotSeen |>> 0, highestBallotAccepted |>> 0, acceptedValue |>> ""])

Prepare(b) ==
    \E p \in Proposers:
        /\ b > Max({ballot \in {msg[3] : msg \in sentMessages} \cup {0}})
        /\ /\* Send prepare message
           \/ /\ decision = ""
              /\ {msg[1]: msg \in sentMessages, msg[2] \in Acceptors, msg[4] = b} \subseteq Proposers
              /\ sentMessages' = sentMessages \cup {[p, "Acceptor", "prepare", b]}
        /\ /\* Send prepare message with decision
           \/ /\ decision /= ""
              /\ {msg[1]: msg \in sentMessages, msg[2] \in Acceptors, msg[4] = b} \subseteq Proposers
              /\ sentMessages' = sentMessages \cup {[p, "Acceptor", "prepare", b]}
              /\ decision' = decision

Promise(p, a, b) ==
    \/ /\ decision = ""
       /\ {msg[1]: msg \in sentMessages, msg[2] = a, msg[3] = "prepare", msg[4] >= b} \subseteq Proposers
       /\ acceptorState[a] = [highestBallotSeen |>> 0, highestBallotAccepted |>> 0, acceptedValue |>> ""]
    \/ /\ decision = ""
       /\ {msg[1]: msg \in sentMessages, msg[2] = a, msg[3] = "prepare", msg[4] >= b} \subseteq Proposers
       /\ acceptorState[a] /= [highestBallotSeen |>> 0, highestBallotAccepted |>> 0, acceptedValue |>> ""]
    \/ /\ decision /= ""
       /\ {msg[1]: msg \in sentMessages, msg[2] = a, msg[3] = "prepare", msg[4] >= b} \subseteq Proposers
       /\ acceptorState[a] = [highestBallotSeen |>> 0, highestBallotAccepted |>> 0, acceptedValue |>> ""]
    \/ /\ decision /= ""
       /\ {msg[1]: msg \in sentMessages, msg[2] = a, msg[3] = "prepare", msg[4] >= b} \subseteq Proposers
       /\ acceptorState[a] /= [highestBallotSeen |>> 0, highestBallotAccepted |>> 0, acceptedValue |>> ""]
    /\ sentMessages' = sentMessages \cup {[a, p, "promise", b, acceptorState[a].highestBallotAccepted, acceptorState[a].acceptedValue]}

Accept(p, v, b) ==
    \/ decision = ""
       /\ {msg[1]: msg \in sentMessages, msg[2] = p, msg[3] = "prepare", msg[4] >= b} \subseteq Acceptors
    /\ sentMessages' = sentMessages \cup {[p, "Acceptor", "accept", b, v]}
    
Accepted(a, p, v, b) ==
    \/ decision = ""
       /\ {msg[1]: msg \in sentMessages, msg[2] = a, msg[3] = "accept", msg[4] = b} \subseteq Proposers
       /\ acceptorState[a].highestBallotSeen < b
    /\ sentMessages' = sentMessages \cup {[a, p, "accepted", b]}
    /\ acceptorState' = [acceptorState EXCEPT ![a] = [highestBallotSeen |>> b, highestBallotAccepted |>> b, acceptedValue |>> v]]

Decide(p, v, b) ==
    \/ decision = ""
       /\ {msg[1]: msg \in sentMessages, msg[2] = a, msg[3] = "accepted", msg[4] = b} \subseteq Acceptors
    /\ decision' = v

Next == 
    \/ \E b \in Nat: Prepare(b)
    \/ \E p \in Proposers, a \in Acceptors, b \in Nat: Promise(p, a, b)
    \/ \E p \in Proposers, v \in Values, b \in Nat: Accept(p, v, b)
    \/ \E a \in Acceptors, p \in Proposers, v \in Values, b \in Nat: Accepted(a, p, v, b)
    \/ \E p \in Proposers, v \in Values, b \in Nat: Decide(p, v, b)

Spec == Init /\ [][Next]_<<sentMessages, decision, acceptorState>>

Safety ==
    /\ \A v \in Values: decision = "" \/ \E msg \in sentMessages: msg[3] = "accept" /\ msg[5] = v

Liveness ==
    FALSE  \* Paxos does not guarantee termination under the asynchronous fault model

\* Fairness conditions
WF == WFNext(Next)

Termination ==
    <>(decision /= "")

THEOREM Spec => []Safety
THEOREM Spec => <>Termination

END paxos
=============================================================================