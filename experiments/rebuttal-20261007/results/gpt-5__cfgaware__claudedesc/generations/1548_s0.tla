---- MODULE OneStepByz ----
EXTENDS Naturals, Integers, FiniteSets

CONSTANTS N, T, F, Proc

VARIABLES pc, nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty

Status == {V0, V1, S0, S1, D0, D1, U0, U1, BYZ}

IsCorrect(i) == pc[i] # BYZ

Tot0 == nSnt0 + nSnt0F
Tot1 == nSnt1 + nSnt1F

vars == << pc, nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty >>

Init ==
  /\ pc \in [Proc -> {V0, V1}]
  /\ nSnt0 = 0
  /\ nSnt1 = 0
  /\ nSnt0F = 0
  /\ nSnt1F = 0
  /\ nRcvd0 = [i \in Proc |-> 0]
  /\ nRcvd1 = [i \in Proc |-> 0]
  /\ nFaulty = 0

Propose(i) ==
  /\ i \in Proc
  /\ IsCorrect(i)
  /\ pc[i] \in {V0, V1}
  /\ pc' = [pc EXCEPT ![i] = IF pc[i] = V0 THEN S0 ELSE S1]
  /\ nSnt0' = nSnt0 + IF pc[i] = V0 THEN 1 ELSE 0
  /\ nSnt1' = nSnt1 + IF pc[i] = V1 THEN 1 ELSE 0
  /\ nSnt0F' = nSnt0F
  /\ nSnt1F' = nSnt1F
  /\ nRcvd0' = nRcvd0
  /\ nRcvd1' = nRcvd1
  /\ nFaulty' = nFaulty

Receive(i) ==
  /\ i \in Proc
  /\ IsCorrect(i)
  /\ \E n0, n1 \in Nat:
       /\ nRcvd0[i] \leq n0 /\ n0 \leq Tot0
       /\ nRcvd1[i] \leq n1 /\ n1 \leq Tot1
       /\ n0 + n1 \leq N
       /\ (n0 > nRcvd0[i] \/ n1 > nRcvd1[i])
       /\ nRcvd0' = [nRcvd0 EXCEPT ![i] = n0]
       /\ nRcvd1' = [nRcvd1 EXCEPT ![i] = n1]
       /\ UNCHANGED << pc, nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty >>

Decide(i) ==
  /\ i \in Proc
  /\ IsCorrect(i)
  /\ pc[i] \in {S0, S1}
  /\ nRcvd0[i] + nRcvd1[i] \geq N - T
  /\ pc' = [ pc EXCEPT
               ![i] =
                 IF nRcvd0[i] \geq N - T THEN D0
                 ELSE IF nRcvd1[i] \geq N - T THEN D1
                 ELSE IF pc[i] = S0 THEN U0 ELSE U1 ]
  /\ UNCHANGED << nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty >>

Faulty(i) ==
  /\ i \in Proc
  /\ LET makeByz == (pc[i] # BYZ) /\ (nFaulty < F)
     IN
       /\ pc' = [pc EXCEPT ![i] = IF makeByz THEN BYZ ELSE @]
       /\ nFaulty' = IF makeByz THEN nFaulty + 1 ELSE nFaulty
       /\ \E a, b \in Nat:
            /\ a \geq nSnt0F /\ b \geq nSnt1F
            /\ a + b \leq nFaulty'
            /\ nSnt0F' = a /\ nSnt1F' = b
       /\ nSnt0' = nSnt0
       /\ nSnt1' = nSnt1
       /\ nRcvd0' = nRcvd0
       /\ nRcvd1' = nRcvd1

Next ==
  \E i \in Proc:
    Propose(i) \/ Receive(i) \/ Decide(i) \/ Faulty(i)

Fairness ==
  /\ \A i \in Proc: WF_vars(Propose(i))
  /\ \A i \in Proc: WF_vars(Receive(i))
  /\ \A i \in Proc: WF_vars(Decide(i))

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Fairness

TypeOK ==
  /\ N \in Nat /\ T \in Nat /\ F \in Nat
  /\ Proc \subseteq Nat \* any finite set of process ids; only cardinality matters
  /\ N = Cardinality(Proc)
  /\ N > 3*T
  /\ F \leq T
  /\ pc \in [Proc -> Status]
  /\ nSnt0 \in Nat /\ nSnt1 \in Nat
  /\ nSnt0F \in Nat /\ nSnt1F \in Nat
  /\ nRcvd0 \in [Proc -> Nat] /\ nRcvd1 \in [Proc -> Nat]
  /\ nFaulty \in Nat /\ nFaulty \leq F
  /\ LET byzSet == { j \in Proc: pc[j] = BYZ } IN nFaulty = Cardinality(byzSet)
  /\ nSnt0F + nSnt1F \leq nFaulty
  /\ \A i \in Proc:
       /\ nRcvd0[i] \leq Tot0
       /\ nRcvd1[i] \leq Tot1
       /\ nRcvd0[i] + nRcvd1[i] \leq N

InitAll0 == \A i \in Proc: pc[i] = V0
InitAll1 == \A i \in Proc: pc[i] = V1

OneStep0_Ltl ==
  InitAll0 => [] (\A i \in Proc: pc[i] \notin {U0, U1, D1})

OneStep1_Ltl ==
  InitAll1 => <> (\A i \in Proc: pc[i] \notin {U0, U1, D0})

AllDecideOne ==
  <> (\A i \in Proc: pc[i] = D1)

====