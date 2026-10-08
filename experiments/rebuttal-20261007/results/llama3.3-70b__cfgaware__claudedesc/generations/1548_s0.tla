--------------------------- MODULE OneStepConsensus ---------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F
VARIABLES nSnt0, nSnt1, nSnt0F, nSnt1F, 
          pc, nRcvd0, nRcvd1, nFaulty

TypeOK == 
  /\ nSnt0 \in Nat
  /\ nSnt1 \in Nat
  /\ nSnt0F \in Nat
  /\ nSnt1F \in Nat
  /\ pc \in [1..N -> {V0, V1, S0, S1, D0, D1, U0, U1, BYZ}]
  /\ nRcvd0 \in [1..N -> Nat]
  /\ nRcvd1 \in [1..N -> Nat]
  /\ nFaulty \in Nat

Propose(i) == 
  IF pc[i] = V0 THEN
    /\ pc' = [pc EXCEPT ![i] = S0]
    /\ nSnt0' = nSnt0 + 1
    /\ nRcvd0' = nRcvd0
    /\ nRcvd1' = nRcvd1
    /\ nFaulty' = nFaulty
    /\ nSnt0F' = nSnt0F
    /\ nSnt1F' = nSnt1F
  ELSE IF pc[i] = V1 THEN
    /\ pc' = [pc EXCEPT ![i] = S1]
    /\ nSnt0' = nSnt0
    /\ nSnt1' = nSnt1 + 1
    /\ nRcvd0' = nRcvd0
    /\ nRcvd1' = nRcvd1
    /\ nFaulty' = nFaulty
    /\ nSnt0F' = nSnt0F
    /\ nSnt1F' = nSnt1F
  ELSE 
    /\ pc' = pc
    /\ nSnt0' = nSnt0
    /\ nSnt1' = nSnt1
    /\ nRcvd0' = nRcvd0
    /\ nRcvd1' = nRcvd1
    /\ nFaulty' = nFaulty
    /\ nSnt0F' = nSnt0F
    /\ nSnt1F' = nSnt1F

Receive(i) == 
  IF pc[i] # BYZ THEN
    /\ pc' = pc
    /\ nSnt0' = nSnt0
    /\ nSnt1' = nSnt1
    /\ nRcvd0' = [nRcvd0 EXCEPT ![i] = Min(nRcvd0[i] + 1, nSnt0 + nSnt0F)]
    /\ nRcvd1' = [nRcvd1 EXCEPT ![i] = Min(nRcvd1[i] + 1, nSnt1 + nSnt1F)]
    /\ nFaulty' = nFaulty
    /\ nSnt0F' = nSnt0F
    /\ nSnt1F' = nSnt1F
  ELSE 
    /\ pc' = pc
    /\ nSnt0' = nSnt0
    /\ nSnt1' = nSnt1
    /\ nRcvd0' = nRcvd0
    /\ nRcvd1' = nRcvd1
    /\ nFaulty' = nFaulty
    /\ nSnt0F' = nSnt0F
    /\ nSnt1F' = nSnt1F

Decide(i) == 
  IF pc[i] # BYZ THEN
    IF (nRcvd0[i] + nRcvd1[i]) >= N - T THEN
      IF nRcvd0[i] > nRcvd1[i] THEN
        /\ pc' = [pc EXCEPT ![i] = D0]
        /\ nSnt0' = nSnt0
        /\ nSnt1' = nSnt1
        /\ nRcvd0' = nRcvd0
        /\ nRcvd1' = nRcvd1
        /\ nFaulty' = nFaulty
        /\ nSnt0F' = nSnt0F
        /\ nSnt1F' = nSnt1F
      ELSE IF nRcvd1[i] > nRcvd0[i] THEN
        /\ pc' = [pc EXCEPT ![i] = D1]
        /\ nSnt0' = nSnt0
        /\ nSnt1' = nSnt1
        /\ nRcvd0' = nRcvd0
        /\ nRcvd1' = nRcvd1
        /\ nFaulty' = nFaulty
        /\ nSnt0F' = nSnt0F
        /\ nSnt1F' = nSnt1F
      ELSE 
        IF pc[i] = S0 THEN
          /\ pc' = [pc EXCEPT ![i] = U0]
          /\ nSnt0' = nSnt0
          /\ nSnt1' = nSnt1
          /\ nRcvd0' = nRcvd0
          /\ nRcvd1' = nRcvd1
          /\ nFaulty' = nFaulty
          /\ nSnt0F' = nSnt0F
          /\ nSnt1F' = nSnt1F
        ELSE 
          /\ pc' = [pc EXCEPT ![i] = U1]
          /\ nSnt0' = nSnt0
          /\ nSnt1' = nSnt1
          /\ nRcvd0' = nRcvd0
          /\ nRcvd1' = nRcvd1
          /\ nFaulty' = nFaulty
          /\ nSnt0F' = nSnt0F
          /\ nSnt1F' = nSnt1F
    ELSE 
      /\ pc' = pc
      /\ nSnt0' = nSnt0
      /\ nSnt1' = nSnt1
      /\ nRcvd0' = nRcvd0
      /\ nRcvd1' = nRcvd1
      /\ nFaulty' = nFaulty
      /\ nSnt0F' = nSnt0F
      /\ nSnt1F' = nSnt1F
  ELSE 
    /\ pc' = pc
    /\ nSnt0' = nSnt0
    /\ nSnt1' = nSnt1
    /\ nRcvd0' = nRcvd0
    /\ nRcvd1' = nRcvd1
    /\ nFaulty' = nFaulty
    /\ nSnt0F' = nSnt0F
    /\ nSnt1F' = nSnt1F

Faulty(i) == 
  IF pc[i] # BYZ THEN
    /\ pc' = [pc EXCEPT ![i] = BYZ]
    /\ nSnt0' = nSnt0
    /\ nSnt1' = nSnt1
    /\ nRcvd0' = nRcvd0
    /\ nRcvd1' = nRcvd1
    /\ nFaulty' = Min(nFaulty + 1, F)
    /\ nSnt0F' = nSnt0F
    /\ nSnt1F' = nSnt1F
  ELSE 
    /\ pc' = pc
    /\ nSnt0' = nSnt0
    /\ nSnt1' = nSnt1
    /\ nRcvd0' = nRcvd0
    /\ nRcvd1' = nRcvd1
    /\ nFaulty' = nFaulty
    /\ nSnt0F' = nSnt0F
    /\ nSnt1F' = nSnt1F

Next == 
  \E i \in (1..N) : Propose(i)
  \/ \E i \in (1..N) : Receive(i)
  \/ \E i \in (1..N) : Decide(i)
  \/ \E i \in (1..N) : Faulty(i)

Spec == 
  /\ Init
  /\ [][Next]_<<nSnt0, nSnt1, nSnt0F, nSnt1F, pc, nRcvd0, nRcvd1, nFaulty>>
  /\ WF_(Propose)(1..N)
  /\ WF_(Receive)(1..N)
  /\ WF_(Decide)(1..N)

Init == 
  /\ nSnt0 = 0
  /\ nSnt1 = 0
  /\ nSnt0F = 0
  /\ nSnt1F = 0
  /\ pc \in [1..N -> {V0, V1}]
  /\ nRcvd0 = [i \in (1..N) |-> 0]
  /\ nRcvd1 = [i \in (1..N) |-> 0]
  /\ nFaulty = 0

OneStep0_Ltl == 
  []~(\E i \in (1..N) : pc[i] \in {U0, U1, D1})

OneStep1_Ltl == 
  <>(\A i \in (1..N) : pc[i] # U0 /\ pc[i] # D0)

AllDecideOne == 
  <>(\A i \in (1..N) : pc[i] = D1)
=============================================================================