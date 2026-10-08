--------------------------- MODULE PaxosSpec ---------------------------
EXTENDS Integers, FiniteSets

CONSTANT Replicas, Ballots, Values
VARIABLE messages, maxBallot, maxVBallot, maxValue, decision

PaxosTypeOK == 
  /\ messages \in [Replicas -> SUBSET (Ballots \x Values)]
  /\ maxBallot \in [Replicas -> Ballots]
  /\ maxVBallot \in [Replicas -> Ballots]
  /\ maxValue \in [Replicas -> Values \cup {<<>>}]
  /\ decision \in Values \cup {<<>>}

PaxosInit == 
  /\ messages = [r \in Replicas |-> {}]
  /\ maxBallot = [r \in Replicas |-> 0]
  /\ maxVBallot = [r \in Replicas |-> 0]
  /\ maxValue = [r \in Replicas |-> <<>>]
  /\ decision = <<>>

PaxosPrepare(r, b) == 
  /\ r \in Replicas
  /\ b \in Ballots
  /\ b # 0
  /\ messages' = [messages EXCEPT ![r] = {<<b, v>> : v \in Values}]
  /\ UNCHANGED <<maxBallot, maxVBallot, maxValue, decision>>

PaxosPromise(r, b) == 
  /\ r \in Replicas
  /\ b \in Ballots
  /\ b > maxBallot[r]
  /\ messages' = [messages EXCEPT ![r] = messages[r] \cup {<<b, v>> : v \in Values}]
  /\ maxBallot' = [maxBallot EXCEPT ![r] = b]
  /\ UNCHANGED <<maxVBallot, maxValue, decision>>

ForcedValue(b) == 
  IF \E r \in Replicas : maxVBallot[r] = b
  THEN CHOOSE v \in Values : \E r \in Replicas : maxVBallot[r] = b /\ maxValue[r] = v
  ELSE CHOOSE v \in Values : TRUE

PaxosAccept(r, b) == 
  /\ r \in Replicas
  /\ b \in Ballots
  /\ {r2 \in Replicas : maxBallot[r2] >= b} = Replicas
  /\ messages' = [messages EXCEPT ![r] = messages[r] \cup {<<b, ForcedValue(b)>>}]
  /\ UNCHANGED <<maxBallot, maxVBallot, maxValue, decision>>

PaxosAccepted(r, b) == 
  /\ r \in Replicas
  /\ b \in Ballots
  /\ b >= maxBallot[r]
  /\ messages' = [messages EXCEPT ![r] = messages[r] \cup {<<b, ForcedValue(b)>>}]
  /\ maxVBallot' = [maxVBallot EXCEPT ![r] = b]
  /\ maxValue' = [maxValue EXCEPT ![r] = ForcedValue(b)]
  /\ UNCHANGED <<maxBallot, decision>>

PaxosDecide(b) == 
  /\ b \in Ballots
  /\ {r \in Replicas : maxVBallot[r] = b} = Replicas
  /\ decision' = ForcedValue(b)
  /\ UNCHANGED <<messages, maxBallot, maxVBallot, maxValue>>

PaxosNontriviality == 
  decision # <<>> => \E r \in Replicas : \E v \in Values : {<<b, v>> : b \in Ballots} \subseteq messages[r]

PaxosConsistency == 
  decision # <<>> => decision' = decision

Next == 
  \/ \E r \in Replicas, b \in Ballots : PaxosPrepare(r, b)
  \/ \E r \in Replicas, b \in Ballots : PaxosPromise(r, b)
  \/ \E r \in Replicas, b \in Ballots : PaxosAccept(r, b)
  \/ \E r \in Replicas, b \in Ballots : PaxosAccepted(r, b)
  \/ \E b \in Ballots : PaxosDecide(b)

Spec == 
  /\ PaxosInit
  /\ [][Next]_<<messages, maxBallot, maxVBallot, maxValue, decision>>
  /\ WF_<<messages, maxBallot, maxVBallot, maxValue, decision>>(PaxosDecide(_))

THEOREM Spec => []PaxosNontriviality
THEOREM Spec => []PaxosConsistency

=============================================================================