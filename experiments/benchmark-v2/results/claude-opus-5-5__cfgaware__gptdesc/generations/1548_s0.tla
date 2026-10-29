------------------------------ MODULE bcons_folklore ------------------------------
(*
  Folklore one-step consensus with Byzantine faults (Dobre & Suri, DSN 2006).
  N processes, at most F of them are Byzantine, and T is the resilience
  threshold assumed by the algorithm.
*)
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ N > 3 * T /\ T >= F

VARIABLES
    nSnt0,    \* number of correct processes that sent 0
    nSnt1,    \* number of correct processes that sent 1
    nRcvd0,   \* nRcvd0[i]: number of 0-messages received by process i
    nRcvd1,   \* nRcvd1[i]: number of 1-messages received by process i
    nFaulty,  \* number of processes that became faulty
    pc        \* control state of each process

vars == << nSnt0, nSnt1, nRcvd0, nRcvd1, nFaulty, pc >>

Proc == 1 .. N

Locations == { "V0", "V1", "S0", "S1", "D0", "D1", "U0", "U1", "BYZ" }

TypeOK ==
    /\ nSnt0 \in 0 .. N
    /\ nSnt1 \in 0 .. N
    /\ nRcvd0 \in [Proc -> 0 .. N]
    /\ nRcvd1 \in [Proc -> 0 .. N]
    /\ nFaulty \in 0 .. F
    /\ pc \in [Proc -> Locations]

Init ==
    /\ nSnt0 = 0
    /\ nSnt1 = 0
    /\ nRcvd0 = [i \in Proc |-> 0]
    /\ nRcvd1 = [i \in Proc |-> 0]
    /\ nFaulty = 0
    /\ pc \in [Proc -> { "V0", "V1" }]

Init0 ==
    /\ nSnt0 = 0
    /\ nSnt1 = 0
    /\ nRcvd0 = [i \in Proc |-> 0]
    /\ nRcvd1 = [i \in Proc |-> 0]
    /\ nFaulty = 0
    /\ pc = [i \in Proc |-> "V0"]

Init1 ==
    /\ nSnt0 = 0
    /\ nSnt1 = 0
    /\ nRcvd0 = [i \in Proc |-> 0]
    /\ nRcvd1 = [i \in Proc |-> 0]
    /\ nFaulty = 0
    /\ pc = [i \in Proc |-> "V1"]

\* A correct process broadcasts its proposal.
Propose(i) ==
    \/ /\ pc[i] = "V0"
       /\ pc' = [pc EXCEPT ![i] = "S0"]
       /\ nSnt0' = nSnt0 + 1
       /\ UNCHANGED << nSnt1, nRcvd0, nRcvd1, nFaulty >>
    \/ /\ pc[i] = "V1"
       /\ pc' = [pc EXCEPT ![i] = "S1"]
       /\ nSnt1' = nSnt1 + 1
       /\ UNCHANGED << nSnt0, nRcvd0, nRcvd1, nFaulty >>

\* A correct process receives a message, possibly from a Byzantine process.
Receive(i) ==
    /\ pc[i] \in { "S0", "S1" }
    /\ \/ /\ nRcvd0[i] < nSnt0 + nFaulty
          /\ nRcvd0' = [nRcvd0 EXCEPT ![i] = nRcvd0[i] + 1]
          /\ UNCHANGED nRcvd1
       \/ /\ nRcvd1[i] < nSnt1 + nFaulty
          /\ nRcvd1' = [nRcvd1 EXCEPT ![i] = nRcvd1[i] + 1]
          /\ UNCHANGED nRcvd0
    /\ UNCHANGED << nSnt0, nSnt1, nFaulty, pc >>

\* After receiving N - T messages, a correct process decides or updates its estimate.
Decide(i) ==
    /\ pc[i] \in { "S0", "S1" }
    /\ nRcvd0[i] + nRcvd1[i] >= N - T
    /\ \/ /\ nRcvd0[i] >= N - T
          /\ pc' = [pc EXCEPT ![i] = "D0"]
       \/ /\ nRcvd1[i] >= N - T
          /\ pc' = [pc EXCEPT ![i] = "D1"]
       \/ /\ nRcvd0[i] < N - T
          /\ nRcvd1[i] < N - T
          /\ nRcvd0[i] >= N - 2 * T
          /\ pc' = [pc EXCEPT ![i] = "U0"]
       \/ /\ nRcvd0[i] < N - T
          /\ nRcvd1[i] < N - T
          /\ nRcvd1[i] >= N - 2 * T
          /\ pc' = [pc EXCEPT ![i] = "U1"]
       \/ /\ nRcvd0[i] < N - 2 * T
          /\ nRcvd1[i] < N - 2 * T
          /\ pc' = [pc EXCEPT ![i] = "U0"]
    /\ UNCHANGED << nSnt0, nSnt1, nRcvd0, nRcvd1, nFaulty >>

\* A process that has not yet sent anything becomes Byzantine.
BecomeFaulty(i) ==
    /\ nFaulty < F
    /\ pc[i] \in { "V0", "V1" }
    /\ pc' = [pc EXCEPT ![i] = "BYZ"]
    /\ nFaulty' = nFaulty + 1
    /\ UNCHANGED << nSnt0, nSnt1, nRcvd0, nRcvd1 >>

Step ==
    \E i \in Proc : Propose(i) \/ Receive(i) \/ Decide(i)

Next ==
    \/ Step
    \/ \E i \in Proc : BecomeFaulty(i)
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

Spec0 == Init0 /\ [][Next]_vars /\ WF_vars(Step)

Spec1 == Init1 /\ [][Next]_vars /\ WF_vars(Step)

\* Safety: no two correct processes decide differently.
Agreement ==
    ~(\E i, j \in Proc : pc[i] = "D0" /\ pc[j] = "D1")

\* If all processes propose 0, then all correct processes eventually decide 0.
OneStep0_Ltl ==
    (\A i \in Proc : pc[i] = "V0")
        => <>(\A i \in Proc : pc[i] \in { "D0", "BYZ" })

\* If all processes propose 1, then all correct processes eventually decide 1.
OneStep1_Ltl ==
    (\A i \in Proc : pc[i] = "V1")
        => <>(\A i \in Proc : pc[i] \in { "D1", "BYZ" })

\* State predicate: all correct processes have decided 1.
AllDecideOne ==
    \A i \in Proc : pc[i] \in { "D1", "BYZ" }

StateConstraint ==
    /\ nSnt0 + nSnt1 + nFaulty <= N
    /\ \A i \in Proc : nRcvd0[i] + nRcvd1[i] <= N

===================================================================================