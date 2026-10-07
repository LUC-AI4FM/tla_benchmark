------------------------------ MODULE OneStepByzConsensus ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

(*
  Parameters and resilience assumptions:
    N > 3T >= 3F >= 0, with N, T, F natural and N >= 1
*)
ASSUME /\ N \in Nat \ {0}
       /\ T \in Nat
       /\ F \in Nat
       /\ N > 3*T
       /\ 3*T >= 3*F

Proc == 1..N

Status == {V0, V1, S0, S1, D0, D1, U0, U1, BYZ}

VARIABLES
  pc,         \* program counter per process
  nSnt0,      \* number of 0-valued broadcasts by correct processes
  nSnt1,      \* number of 1-valued broadcasts by correct processes
  nSnt0F,     \* number of 0-valued messages injected by faulty processes
  nSnt1F,     \* number of 1-valued messages injected by faulty processes
  nRcvd0,     \* per-process received count of 0-valued messages
  nRcvd1,     \* per-process received count of 1-valued messages
  nFaulty     \* number of Byzantine processes

vars == << pc, nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty >>

Threshold == N - T

TotalSent0 == nSnt0 + nSnt0F
TotalSent1 == nSnt1 + nSnt1F

TotalRecv(i) == nRcvd0[i] + nRcvd1[i]

FaultySet == { i \in Proc : pc[i] = BYZ }

TypeOK ==
  /\ pc \in [Proc -> Status]
  /\ nSnt0 \in Nat /\ nSnt1 \in Nat
  /\ nSnt0F \in Nat /\ nSnt1F \in Nat
  /\ nFaulty \in Nat
  /\ nRcvd0 \in [Proc -> Nat]
  /\ nRcvd1 \in [Proc -> Nat]
  /\ nSnt0 <= N /\ nSnt1 <= N
  /\ nSnt0 + nSnt1 <= N
  /\ nSnt0F <= nFaulty /\ nSnt1F <= nFaulty
  /\ nFaulty = Cardinality(FaultySet)
  /\ nFaulty <= F
  /\ \A i \in Proc:
        /\ nRcvd0[i] <= TotalSent0
        /\ nRcvd1[i] <= TotalSent1

Init ==
  /\ pc \in [Proc -> {V0, V1}]
  /\ nSnt0 = 0 /\ nSnt1 = 0
  /\ nSnt0F = 0 /\ nSnt1F = 0
  /\ nRcvd0 = [i \in Proc |-> 0]
  /\ nRcvd1 = [i \in Proc |-> 0]
  /\ nFaulty = 0
  /\ TypeOK

Propose(i) ==
  /\ i \in Proc
  /\ pc[i] \in {V0, V1}
  /\ IF pc[i] = V0
        THEN /\ pc' = [pc EXCEPT ![i] = S0]
             /\ nSnt0' = nSnt0 + 1
             /\ nSnt1' = nSnt1
        ELSE /\ pc' = [pc EXCEPT ![i] = S1]
             /\ nSnt1' = nSnt1 + 1
             /\ nSnt0' = nSnt0
  /\ UNCHANGED << nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty >>

Receive(i) ==
  /\ i \in Proc
  /\ pc[i] # BYZ
  /\ (nRcvd0[i] < TotalSent0 \/ nRcvd1[i] < TotalSent1)
  /\ \E r0, r1 \in Nat:
       /\ nRcvd0[i] <= r0 /\ r0 <= TotalSent0
       /\ nRcvd1[i] <= r1 /\ r1 <= TotalSent1
       /\ (r0 > nRcvd0[i] \/ r1 > nRcvd1[i])
       /\ nRcvd0' = [nRcvd0 EXCEPT ![i] = r0]
       /\ nRcvd1' = [nRcvd1 EXCEPT ![i] = r1]
  /\ UNCHANGED << pc, nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty >>

Decide(i) ==
  /\ i \in Proc
  /\ pc[i] \in {S0, S1}
  /\ TotalRecv(i) >= Threshold
  /\ pc' = [ pc EXCEPT
              ![i] =
                IF (nRcvd0[i] >= Threshold) /\ ~(nRcvd1[i] >= Threshold) THEN D0
                ELSE IF (nRcvd1[i] >= Threshold) /\ ~(nRcvd0[i] >= Threshold) THEN D1
                ELSE IF pc[i] = S0 THEN U0 ELSE U1
           ]
  /\ UNCHANGED << nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty >>

Faulty(i) ==
  /\ i \in Proc
  /\ pc[i] # BYZ
  /\ nFaulty < F
  /\ \E f0, f1 \in Nat:
       /\ f0 >= nSnt0F /\ f1 >= nSnt1F
       /\ f0 <= nFaulty + 1 /\ f1 <= nFaulty + 1
       /\ nSnt0F' = f0 /\ nSnt1F' = f1
  /\ pc' = [pc EXCEPT ![i] = BYZ]
  /\ nFaulty' = nFaulty + 1
  /\ UNCHANGED << nSnt0, nSnt1, nRcvd0, nRcvd1 >>

Next ==
  \E i \in Proc:
    Propose(i) \/ Receive(i) \/ Decide(i) \/ Faulty(i)

Fairness ==
  \A i \in Proc:
    /\ WF_vars(Propose(i))
    /\ WF_vars(Receive(i))
    /\ WF_vars(Decide(i))

Spec ==
  Init /\ [][Next]_vars /\ Fairness

(*
  Validity/liveness properties for model checking
*)

AllStart0 == \A i \in Proc: pc[i] = V0
AllStart1 == \A i \in Proc: pc[i] = V1

NoUorD1 == \A i \in Proc: pc[i] \notin {U0, U1, D1}
NoUorD0 == \A i \in Proc: pc[i] \notin {U0, U1, D0}

ValidIfAllZeroNeverUorD1 ==
  AllStart0 => [] NoUorD1

ValidIfAllOneEventuallyNoUorD0 ==
  AllStart1 => <> NoUorD0

AllDecideOne ==
  \A i \in Proc: <> (pc[i] = D1)

=============================================================================