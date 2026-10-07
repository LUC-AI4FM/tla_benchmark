```
MODULE ByzantineConsensus
EXTENDS Integers, TLC

CONSTANTS N, T, F, V0, V1
VARIABLES nSnt0, nSnt1, nSnt0F, nSnt1F,
          nRcvd0, nRcvd1, pc, nFaulty

Init ==
  /\ nSnt0 = 0
  /\ nSnt1 = 0
  /\ nSnt0F = 0
  /\ nSnt1F = 0
  /\ nRcvd0 = [i \in 1..N |-> 0]
  /\ nRcvd1 = [i \in 1..N |-> 0]
  /\ pc = [i \in 1..N |-> IF i <= N - F THEN V0 ELSE BYZ]
  /\ nFaulty = 0

TypeOK ==
  /\ nSnt0 >= 0
  /\ nSnt1 >= 0
  /\ nSnt0F >= 0
  /\ nSnt1F >= 0
  /\ nRcvd0 \in [i \in 1..N |-> Nat]
  /\ nRcvd1 \in [i \in 1..N |-> Nat]
  /\ pc \in [i \in 1..N |-> {V0, V1, S0, S1, D0, D1, U0, U1, BYZ}]
  /\ nFaulty >= 0

Propose(i) ==
  IF pc[i] = V0
  THEN
    /\ nSnt0' = nSnt0 + 1
    /\ pc' = [pc EXCEPT ![i] = S0]
    /\ UNCHANGED <<nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty>>
  ELSE IF pc[i] = V1
  THEN
    /\ nSnt1' = nSnt1 + 1
    /\ pc' = [pc EXCEPT ![i] = S1]
    /\ UNCHANGED <<nSnt0, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty>>
  ELSE
    UNCHANGED <<nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, pc, nFaulty>>

Receive(i) ==
  IF pc[i] # BYZ
  THEN
    /\ nRcvd0' = [nRcvd0 EXCEPT ![i] = Min(nRcvd0[i] + 1, nSnt0 + nSnt0F)]
    /\ nRcvd1' = [nRcvd1 EXCEPT ![i] = Min(nRcvd1[i] + 1, nSnt1 + nSnt1F)]
    /\ UNCHANGED <<nSnt0, nSnt1, nSnt0F, nSnt1F, pc, nFaulty>>
  ELSE
    UNCHANGED <<nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, pc, nFaulty>>

Decide(i) ==
  IF pc[i] = S0 /\ (nRcvd0[i] + nRcvd1[i]) >= N - T
  THEN
    IF nRcvd0[i] > nRcvd1[i]
    THEN
      /\ pc' = [pc EXCEPT ![i] = D0]
      /\ UNCHANGED <<nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty>>
    ELSE IF nRcvd0[i] < nRcvd1[i]
    THEN
      /\ pc' = [pc EXCEPT ![i] = D1]
      /\ UNCHANGED <<nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty>>
    ELSE
      /\ pc' = [pc EXCEPT ![i] = U0]
      /\ UNCHANGED <<nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty>>
  ELSE IF pc[i] = S1 /\ (nRcvd0[i] + nRcvd1[i]) >= N - T
  THEN
    IF nRcvd0[i] > nRcvd1[i]
    THEN
      /\ pc' = [pc EXCEPT ![i] = D0]
      /\ UNCHANGED <<nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty>>
    ELSE IF nRcvd0[i] < nRcvd1[i]
    THEN
      /\ pc' = [pc EXCEPT ![i] = D1]
      /\ UNCHANGED <<nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty>>
    ELSE
      /\ pc' = [pc EXCEPT ![i] = U1]
      /\ UNCHANGED <<nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty>>
  ELSE
    UNCHANGED <<nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, pc, nFaulty>>

Faulty(i) ==
  IF pc[i] # BYZ /\ nFaulty < F
  THEN
    /\ pc' = [pc EXCEPT ![i] = BYZ]
    /\ nFaulty' = nFaulty + 1
    /\ UNCHANGED <<nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1>>
  ELSE
    UNCHANGED <<nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, pc, nFaulty>>

Next ==
  \/ \E i \in 1..N : Propose(i)
  \/ \E i \in 1..N : Receive(i)
  \/ \E i \in 1..N : Decide(i)
  \/ \E i \in 1..N : Faulty(i)

Spec == Init /\ [][Next]_<<nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, pc, nFaulty>>
          /\ WF_Vars(Propose)
          /\ WF_Vars(Receive)
          /\ WF_Vars(Decide)

THEOREM Spec => []TypeOK
THEOREM Spec => []( \A i \in 1..N : pc[i] = V0 ) => []( \A i \in 1..N : pc[i] # U1 /\ pc[i] # D1 )
THEOREM Spec => []( \A i \in 1..N : pc[i] = V1 ) => <>( \A i \in 1..N : pc[i] # U0 /\ pc[i] # D0 )
THEOREM Spec => []<>( \E i \in 1..N : pc[i] = D1 )

AllDecideOne == []( \A i \in 1..N : pc[i] = D1 )
```