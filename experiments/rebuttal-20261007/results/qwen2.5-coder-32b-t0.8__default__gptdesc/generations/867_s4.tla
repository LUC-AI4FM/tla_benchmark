------------------------------ MODULE Paxos ------------------------------

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Proposers, Acceptors, Values

VARIABLES sentMessages, decision, acceptorState

(* A message is a tuple: <<type, sender, ballot, value>> *)
MsgType == {"prepare", "promise", "accept", "accepted", "decide"}

Ballot == [b \in 1..2 : Nat]

Prepare(b) == << "prepare", _, b, _ >>

Promise(a, b) == << "promise", a, b, _ >>

Accept(p, b, v) == << "accept", p, b, v >>

Accepted(a, b, v) == << "accepted", a, b, v >>

Decide(v) == << "decide", _, _, v >>

SentMessagesInit == {}

AcceptorStateInit == [a \in Acceptors |-> [highestSeenBallot |-> Ballot'[-1], highestAcceptedBallot |-> Ballot'[-1], acceptedValue |-> _]]

Init ==
    /\ sentMessages = SentMessagesInit
    /\ decision = << >>
    /\ acceptorState = AcceptorStateInit

Next ==
    \/ \E m \in MsgType, p \in Proposers, a \in Acceptors, b \in Ballot, v \in Values :
        \/ /\ m = "prepare"
           /\ sentMessages' = sentMessages \cup {Prepare(b)}
        \/ /\ m = "promise"
           /\ [a] \in Domain(sentMessages)
           /\ sentMessages[a] = Prepare(b)
           /\ LET highestSeen = acceptorState[a].highestSeenBallot
              highestAccepted = acceptorState[a].highestAcceptedBallot
              acceptedVal = IF b > highestSeen THEN Ballot'[-1] ELSE acceptorState[a].acceptedValue
          IN sentMessages' = sentMessages \cup {Promise(a, b)}
             /\ acceptorState' = [acceptorState EXCEPT ![a] = [highestSeenBallot |-> b, acceptedValue |-> acceptedVal]]
        \/ /\ m = "accept"
           /\ [p] \in Domain(sentMessages)
           /\ LET prepMsg = sentMessages[p]
              ballotPrep = prepMsg[2]
          IN ballotPrep = b
             /\ sentMessages' = sentMessages \cup {Accept(p, b, v)}
        \/ /\ m = "accepted"
           /\ [a] \in Domain(sentMessages)
           /\ LET accMsg = sentMessages[a]
              ballotAcc = accMsg[2]
              valAcc = accMsg[3]
          IN ballotAcc = b
             /\ sentMessages' = sentMessages \cup {Accepted(a, b, valAcc)}
        \/ /\ m = "decide"
           /\ decision = << >>
           /\ LET quorumSize = (Cardinality(Acceptors) DIV 2) + 1
              acceptedVals = [a \in Acceptors |-> acceptorState[a].acceptedValue]
              valueCounts = [v \in Values |-> Cardinality({a \in Acceptors : acceptedVals[a] = v})]
          IN \E v \in DOMAIN valueCounts :
             valueCounts[v] >= quorumSize
                /\ decision' = Decide(v)

Spec ==
    /\ Init
    /\ [][Next]_<<sentMessages, decision, acceptorState>>
    /\ <>[]decision # << >>

InvariantNonTriviality ==
    \/ decision = << >>
    \/ \E v \in Values : decision = Decide(v) /\ \E m \in sentMessages : m[1] = "accept" /\ m[3] = v

InvariantConsistency ==
    \/ decision = << >>
    \/ \A a \in Acceptors :
        LET highestSeen = acceptorState[a].highestSeenBallot
            highestAccepted = acceptorState[a].highestAcceptedBallot
            acceptedVal = acceptorState[a].acceptedValue
        IN (highestSeen = Ballot'[-1]) \/ (highestAccepted <= highestSeen /\ decision[3] = acceptedVal)

(* Liveness is explicitly set to FALSE as Paxos does not guarantee termination under the asynchronous fault model implied by FLP-style reasoning. *)
Liveness == FALSE

=============================================================================