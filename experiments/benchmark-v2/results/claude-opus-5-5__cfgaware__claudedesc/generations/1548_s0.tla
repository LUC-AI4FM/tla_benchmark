------------------------------- MODULE OneStepByz -------------------------------
(* Threshold-based one-step Byzantine consensus (Algorithm 2, Dobre & Suri 2006). *)
EXTENDS Naturals

CONSTANTS N, T, F

ASSUME N \in Nat /\ T \in Nat /\ F \in Nat
ASSUME (N > 3 * T) /\ (T >= F) /\ (F >= 0)

VARIABLES pc, nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty, nRcvd0, nRcvd1

vars == << pc, nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty, nRcvd0, nRcvd1 >>

Proc == 1 .. N

Status == { "V0", "V1", "S0", "S1", "D0", "D1", "U0", "U1", "BYZ" }

Init ==
  /\ pc \in [ Proc -> { "V0", "V1" } ]
  /\ nSnt0 = 0
  /\ nSnt1 = 0
  /\ nSnt0F = 0
  /\ nSnt1F = 0
  /\ nFaulty = 0
  /\ nRcvd0 = [ i \in Proc |-> 0 ]
  /\ nRcvd1 = [ i \in Proc |-> 0 ]

Propose(i) ==
  \/ /\ pc[i] = "V0"
     /\ pc' = [ pc EXCEPT ![i] = "S0" ]
     /\ nSnt0' = nSnt0 + 1
     /\ UNCHANGED << nSnt1, nSnt0F, nSnt1F, nFaulty, nRcvd0, nRcvd1 >>
  \/ /\ pc[i] = "V1"
     /\ pc' = [ pc EXCEPT ![i] = "S1" ]
     /\ nSnt1' = nSnt1 + 1
     /\ UNCHANGED << nSnt0, nSnt0F, nSnt1F, nFaulty, nRcvd0, nRcvd1 >>

Receive(i) ==
  /\ pc[i] # "BYZ"
  /\ \/ /\ nRcvd0[i] < nSnt0 + nSnt0F
        /\ nRcvd0' = [ nRcvd0 EXCEPT ![i] = nRcvd0[i] + 1 ]
        /\ UNCHANGED nRcvd1
     \/ /\ nRcvd1[i] < nSnt1 + nSnt1F
        /\ nRcvd1' = [ nRcvd1 EXCEPT ![i] = nRcvd1[i] + 1 ]
        /\ UNCHANGED nRcvd0
  /\ UNCHANGED << pc, nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty >>

Decide(i) ==
  /\ pc[i] \in { "S0", "S1" }
  /\ nRcvd0[i] + nRcvd1[i] >= N - T
  /\ \/ /\ nRcvd0[i] >= N - T
        /\ pc' = [ pc EXCEPT ![i] = "D0" ]
     \/ /\ nRcvd1[i] >= N - T
        /\ pc' = [ pc EXCEPT ![i] = "D1" ]
     \/ /\ nRcvd0[i] < N - T
        /\ nRcvd1[i] < N - T
        /\ nRcvd0[i] >= nRcvd1[i]
        /\ pc' = [ pc EXCEPT ![i] = "U0" ]
     \/ /\ nRcvd0[i] < N - T
        /\ nRcvd1[i] < N - T
        /\ nRcvd0[i] < nRcvd1[i]
        /\ pc' = [ pc EXCEPT ![i] = "U1" ]
  /\ UNCHANGED << nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty, nRcvd0, nRcvd1 >>

Faulty(i) ==
  /\ pc[i] # "BYZ"
  /\ nFaulty < F
  /\ pc' = [ pc EXCEPT ![i] = "BYZ" ]
  /\ nFaulty' = nFaulty + 1
  /\ nSnt0F' = nSnt0F + 1
  /\ nSnt1F' = nSnt1F + 1
  /\ UNCHANGED << nSnt0, nSnt1, nRcvd0, nRcvd1 >>

Next == \E i \in Proc : Propose(i) \/ Receive(i) \/ Decide(i) \/ Faulty(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E i \in Proc : Propose(i))
  /\ WF_vars(\E i \in Proc : Receive(i))
  /\ WF_vars(\E i \in Proc : Decide(i))

TypeOK ==
  /\ pc \in [ Proc -> Status ]
  /\ nSnt0 \in 0 .. N
  /\ nSnt1 \in 0 .. N
  /\ nSnt0F \in 0 .. N
  /\ nSnt1F \in 0 .. N
  /\ nFaulty \in 0 .. F
  /\ nRcvd0 \in [ Proc -> 0 .. (2 * N) ]
  /\ nRcvd1 \in [ Proc -> 0 .. (2 * N) ]

StateConstraint ==
  /\ nSnt0 + nSnt0F <= 2 * N
  /\ nSnt1 + nSnt1F <= 2 * N
  /\ nFaulty <= F

OneStep0_Ltl ==
  (\A i \in Proc : pc[i] = "V0")
    => [](\A i \in Proc : pc[i] \notin { "U0", "U1", "D1" })

OneStep1_Ltl ==
  (\A i \in Proc : pc[i] = "V1")
    => <>(\A i \in Proc : pc[i] \notin { "U0", "U1", "D0" })

AllDecideOne == <>(\A i \in Proc : pc[i] = "D1")

=============================================================================