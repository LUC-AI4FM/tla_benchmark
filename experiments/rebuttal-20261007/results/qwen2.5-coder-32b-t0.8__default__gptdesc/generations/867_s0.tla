------------------------------- MODULE Paxos -------------------------------

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
  PROPOSERS, ACCEPTORS, VALS

VARIABLES
  sentMessages,
  decidedValue,
  acceptorState \* [acceptor \in ACCEPTORS -> <<highestBallotSeen, highestBallotAccepted, acceptedValue>>]

Init ==
  /\ sentMessages = {}
  /\ decidedValue = <<FALSE, _>>
  /\ (\A a \in ACCEPTORS: acceptorState[a] = <<0, 0, _>>)

Prepare(ballot) ==
  \/ EXIST pro \in PROPOSERS:
     /\ <<pro, "prepare", ballot>> \notin sentMessages
     /\ {<<pro, "prepare", ballot>>} \cup sentMessages \in SUBSETEQ (PROPOSERS \X {"prepare"} \X Nat)

Promise(ballot, acceptor) ==
  \/ EXIST prep \in PROPOSERS:
     /\ <<prep, "promise", ballot, _>> \notin sentMessages
     /\ LET hbSeen = acceptorState[acceptor][1]
          hbAccepted = acceptorState[acceptor][2]
          acceptedVal = acceptorState[acceptor][3] IN
        {<<prep, "promise", ballot, <<hbSeen, hbAccepted, acceptedVal>> >>} \cup sentMessages \in SUBSETEQ (PROPOSERS \X {"promise"} \X Nat \X (Nat \X Nat \X VALS))

Accept(ballot, value) ==
  \/ EXIST prep \in PROPOSERS:
     /\ <<prep, "accept", ballot, value>> \notin sentMessages
     /\ {<<prep, "accept", ballot, value>>} \cup sentMessages \in SUBSETEQ (PROPOSERS \X {"accept"} \X Nat \X VALS)

Accepted(ballot, value, acceptor) ==
  \/ EXIST prep \in PROPOSERS:
     /\ <<prep, "accepted", ballot, value, acceptor>> \notin sentMessages
     /\ LET hbSeen = [acceptorState[acceptor] EXCEPT ![1] = ballot]
          hbAccepted = ballot
          acceptedVal = value IN
        {<<prep, "accepted", ballot, value, acceptor>>} \cup sentMessages \in SUBSETEQ (PROPOSERS \X {"accepted"} \X Nat \X VALS)
     /\ /\ ballot >= acceptorState[acceptor][1]
        /\ ballot >= acceptorState[acceptor][2]
        /\ acceptorState' = [acceptorState EXCEPT ![acceptor] = <<hbSeen, hbAccepted, acceptedVal>>]

Decide(ballot, value) ==
  \/ EXIST prep \in PROPOSERS:
     /\ <<prep, "decide", ballot, value>> \notin sentMessages
     /\ {<<prep, "decide", ballot, value>>} \cup sentMessages \in SUBSETEQ (PROPOSERS \X {"decide"} \X Nat \X VALS)
     /\ decidedValue' = <<TRUE, value>>

Next ==
  \/ \/ Prepare(sentMessages)
     \/ \/ /\ Promise(sentMessages)
            /\ Accept(sentMessages)
           \/ Accepted(sentMessages)
     \/ Decide(sentMessages)

Spec ==
  Init /\ [][Next]_<<sentMessages, decidedValue, acceptorState>> /\ WF_next(<<sentMessages, decidedValue, acceptorState>>)

\* Safety properties
TypeOk ==
  /\ sentMessages \in SUBSETEQ (PROPOSERS \X {"prepare", "promise", "accept", "accepted", "decide"} \X Nat \X (Nat \X Nat \X VALS))
  /\ decidedValue \in BOOLEAN \X VALS

NonTriviality ==
  \/ decidedValue[1] = FALSE
  \/ \E v \in VALS: decidedValue = <<TRUE, v>> /\ (\E m \in sentMessages: EXIST prep \in PROPOSERS, ballot \in Nat: m = <<prep, "accept", ballot, v>>)

Consistency ==
  \A pro1, pro2 \in PROPOSERS, ballot1, ballot2 \in Nat, val1, val2 \in VALS:
     /\ <<pro1, "decide", ballot1, val1>> \in sentMessages
     /\ <<pro2, "decide", ballot2, val2>> \in sentMessages
     => val1 = val2

\* Liveness properties (explicitly set to FALSE)
Liveness ==
  FALSE

=============================================================================