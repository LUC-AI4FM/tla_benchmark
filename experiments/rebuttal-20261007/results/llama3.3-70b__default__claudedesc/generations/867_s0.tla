```tla
MODULE Paxos
EXTENDS Integers, FiniteSets

CONSTANTS Replicas, Ballots, Values
VARIABLES messages,
          maxBallot,
          maxVBallot,
          maxValue,
          decision

Init ==
  /\ messages = {}
  /\ maxBallot = [r \in Replicas |-> 0]
  /\ maxVBallot = [r \in Replicas |-> 0]
  /\ maxValue = [r \in Replicas |-> NULL]
  /\ decision = NULL

PaxosPrepare(b) ==
  /\ b \in Ballots
  /\ b # 0
  /\ messages' = messages \cup {<<"Prepare", b>>}
  /\ UNCHANGED <<maxBallot, maxVBallot, maxValue, decision>>

PaxosPromise(r, b) ==
  /\ r \in Replicas
  /\ b \in Ballots
  /\ b > maxBallot[r]
  /\ messages' = messages \cup {<<"Promise", r, b>>}
  /\ maxBallot' = [maxBallot EXCEPT ![r] = b]
  /\ UNCHANGED <<maxVBallot, maxValue, decision>>

ForcedValue(b) ==
  IF \E r \in Replicas : maxVBallot[r] # 0
  THEN CHOOSE v \in Values : \E r \in Replicas : maxVBallot[r] = b /\ maxValue[r] = v
  ELSE CHOOSE v \in Values : TRUE

PaxosAccept(b, v) ==
  /\ b \in Ballots
  /\ {r \in Replicas : << "Promise", r, b >> \in messages} = Replicas
  /\ v = ForcedValue(b)
  /\ messages' = messages \cup {<<"Accept", b, v>>}
  /\ UNCHANGED <<maxBallot, maxVBallot, maxValue, decision>>

PaxosAccepted(r, b, v) ==
  /\ r \in Replicas
  /\ b \in Ballots
  /\ b >= maxBallot[r]
  /\ {<<"Accept", b, v>>} \subseteq messages
  /\ messages' = messages \cup {<<"Accepted", r, b, v>>}
  /\ maxVBallot' = [maxVBallot EXCEPT ![r] = b]
  /\ maxValue' = [maxValue EXCEPT ![r] = v]
  /\ UNCHANGED <<maxBallot, decision>>

PaxosDecide(b, v) ==
  /\ b \in Ballots
  /\ {r \in Replicas : << "Accepted", r, b, v >> \in messages} = Replicas
  /\ decision' = v
  /\ UNCHANGED <<messages, maxBallot, maxVBallot, maxValue>>

Next ==
  \/ \E b \in Ballots : PaxosPrepare(b)
  \/ \E r \in Replicas, b \in Ballots : PaxosPromise(r, b)
  \/ \E b \in Ballots, v \in Values : PaxosAccept(b, v)
  \/ \E r \in Replicas, b \in Ballots, v \in Values : PaxosAccepted(r, b, v)
  \/ \E b \in Ballots, v \in Values : PaxosDecide(b, v)

PaxosNontriviality ==
  decision # NULL => \E r \in Replicas : \E b \in Ballots : maxVBallot[r] = b /\ maxValue[r] = decision

PaxosConsistency ==
  decision # NULL => Box(decision' = decision)

Spec ==
  Init /\ [][Next]_<<messages, maxBallot, maxVBallot, maxValue, decision>>
  /\ WF_<<messages, maxBallot, maxVBallot, maxValue, decision>>(PaxosDecide(_, _))
  /\ []PaxosNontriviality
  /\ []PaxosConsistency

THEOREM Spec => FALSE
```