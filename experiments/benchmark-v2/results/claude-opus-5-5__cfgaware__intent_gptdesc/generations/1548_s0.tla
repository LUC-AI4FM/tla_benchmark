------------------------------ MODULE OneStepByz ------------------------------
EXTENDS Naturals

CONSTANTS N, T, F

ASSUME /\ N \in Nat /\ T \in Nat /\ F \in Nat
       /\ N > 3 * T
       /\ T >= F

Proc == 1 .. N

States == {"V0", "V1", "S0", "S1", "D0", "D1", "U0", "U1", "BYZ"}

VARIABLES pc,       \* local control state of every process
          nSnt0,    \* number of 0-votes sent by correct processes
          nSnt1,    \* number of 1-votes sent by correct processes
          nFaulty,  \* number of processes that became Byzantine
          nRcvd0,   \* number of 0-votes received by each process
          nRcvd1    \* number of 1-votes received by each process

vars == << pc, nSnt0, nSnt1, nFaulty, nRcvd0, nRcvd1 >>

-----------------------------------------------------------------------------
Init ==
  /\ pc \in [Proc -> {"V0", "V1"}]
  /\ nSnt0 = 0
  /\ nSnt1 = 0
  /\ nFaulty = 0
  /\ nRcvd0 = [i \in Proc |-> 0]
  /\ nRcvd1 = [i \in Proc |-> 0]

\* A process that has not yet broadcast may become Byzantine (at most F).
BecomeByzantine(i) ==
  /\ pc[i] \in {"V0", "V1"}
  /\ nFaulty < F
  /\ nFaulty' = nFaulty + 1
  /\ pc' = [pc EXCEPT ![i] = "BYZ"]
  /\ UNCHANGED << nSnt0, nSnt1, nRcvd0, nRcvd1 >>

\* A correct process makes its single broadcast of its proposal.
Send0(i) ==
  /\ pc[i] = "V0"
  /\ nSnt0' = nSnt0 + 1
  /\ pc' = [pc EXCEPT ![i] = "S0"]
  /\ UNCHANGED << nSnt1, nFaulty, nRcvd0, nRcvd1 >>

Send1(i) ==
  /\ pc[i] = "V1"
  /\ nSnt1' = nSnt1 + 1
  /\ pc' = [pc EXCEPT ![i] = "S1"]
  /\ UNCHANGED << nSnt0, nFaulty, nRcvd0, nRcvd1 >>

Send(i) == Send0(i) \/ Send1(i)

\* Receive one more vote; Byzantine processes may forge votes of either value.
Receive0(i) ==
  /\ pc[i] # "BYZ"
  /\ nRcvd0[i] < nSnt0 + nFaulty
  /\ nRcvd0' = [nRcvd0 EXCEPT ![i] = @ + 1]
  /\ UNCHANGED << pc, nSnt0, nSnt1, nFaulty, nRcvd1 >>

Receive1(i) ==
  /\ pc[i] # "BYZ"
  /\ nRcvd1[i] < nSnt1 + nFaulty
  /\ nRcvd1' = [nRcvd1 EXCEPT ![i] = @ + 1]
  /\ UNCHANGED << pc, nSnt0, nSnt1, nFaulty, nRcvd0 >>

Receive(i) == Receive0(i) \/ Receive1(i)

\* Decision rule: requires at least N - T votes in total.
Decide(i) ==
  /\ pc[i] \in {"S0", "S1"}
  /\ nRcvd0[i] + nRcvd1[i] >= N - T
  /\ \/ /\ nRcvd0[i] >= N - T
        /\ pc' = [pc EXCEPT ![i] = "D0"]
     \/ /\ nRcvd1[i] >= N - T
        /\ pc' = [pc EXCEPT ![i] = "D1"]
     \/ /\ nRcvd0[i] < N - T
        /\ nRcvd1[i] < N - T
        /\ pc' = [pc EXCEPT ![i] = IF pc[i] = "S0" THEN "U0" ELSE "U1"]
  /\ UNCHANGED << nSnt0, nSnt1, nFaulty, nRcvd0, nRcvd1 >>

Next ==
  \E i \in Proc :
     \/ BecomeByzantine(i)
     \/ Send(i)
     \/ Receive(i)
     \/ Decide(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in Proc : WF_vars(Send(i))
  /\ \A i \in Proc : WF_vars(Receive(i))
  /\ \A i \in Proc : WF_vars(Decide(i))

-----------------------------------------------------------------------------
TypeOK ==
  /\ pc \in [Proc -> States]
  /\ nSnt0 \in 0 .. N
  /\ nSnt1 \in 0 .. N
  /\ nFaulty \in 0 .. F
  /\ nRcvd0 \in [Proc -> 0 .. N]
  /\ nRcvd1 \in [Proc -> 0 .. N]
  /\ nSnt0 + nSnt1 + nFaulty <= N

StateConstraint ==
  /\ nSnt0 \in 0 .. N
  /\ nSnt1 \in 0 .. N
  /\ nFaulty \in 0 .. F
  /\ \A i \in Proc : nRcvd0[i] \in 0 .. N /\ nRcvd1[i] \in 0 .. N

\* Safety: if all processes propose 0, no correct process decides 1.
OneStep0_Ltl ==
  (\A i \in Proc : pc[i] = "V0") =>
     [](\A i \in Proc : pc[i] # "D1" /\ pc[i] # "U1")

\* Safety: if all processes propose 1, no correct process decides 0.
OneStep1_Ltl ==
  (\A i \in Proc : pc[i] = "V1") =>
     [](\A i \in Proc : pc[i] # "D0" /\ pc[i] # "U0")

\* Liveness: if all propose 1, every correct process eventually reaches a
\* terminal state consistent with the thresholds.
AllDecideOne ==
  (\A i \in Proc : pc[i] = "V1") =>
     <>(\A i \in Proc : pc[i] \in {"D1", "U1", "BYZ"})

=============================================================================