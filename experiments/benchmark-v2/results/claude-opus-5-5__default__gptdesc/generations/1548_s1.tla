------------------------------ MODULE cf1s_folklore ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ N > 5 * T /\ T >= F /\ F >= 0

VARIABLES nSnt0,    \* number of 0-messages sent by correct processes
          nSnt1,    \* number of 1-messages sent by correct processes
          nFaulty,  \* number of Byzantine processes
          pc,       \* control state of each process
          nRcvd0,   \* number of 0-messages received by each process
          nRcvd1    \* number of 1-messages received by each process

vars == << nSnt0, nSnt1, nFaulty, pc, nRcvd0, nRcvd1 >>

Proc == 1 .. N

Status == { "V0", "V1", "S0", "S1", "D0", "D1", "U0", "U1", "BYZ" }

Correct(i) == pc[i] # "BYZ"

TypeOK ==
  /\ nSnt0 \in 0 .. N
  /\ nSnt1 \in 0 .. N
  /\ nFaulty \in 0 .. F
  /\ pc \in [ Proc -> Status ]
  /\ nRcvd0 \in [ Proc -> 0 .. N ]
  /\ nRcvd1 \in [ Proc -> 0 .. N ]

\* Generic initial states: each process proposes 0 or 1
Init ==
  /\ nSnt0 = 0
  /\ nSnt1 = 0
  /\ nFaulty = 0
  /\ pc \in [ Proc -> { "V0", "V1" } ]
  /\ nRcvd0 = [ i \in Proc |-> 0 ]
  /\ nRcvd1 = [ i \in Proc |-> 0 ]

\* All processes propose 0
Init0 ==
  /\ nSnt0 = 0
  /\ nSnt1 = 0
  /\ nFaulty = 0
  /\ pc = [ i \in Proc |-> "V0" ]
  /\ nRcvd0 = [ i \in Proc |-> 0 ]
  /\ nRcvd1 = [ i \in Proc |-> 0 ]

\* All processes propose 1
Init1 ==
  /\ nSnt0 = 0
  /\ nSnt1 = 0
  /\ nFaulty = 0
  /\ pc = [ i \in Proc |-> "V1" ]
  /\ nRcvd0 = [ i \in Proc |-> 0 ]
  /\ nRcvd1 = [ i \in Proc |-> 0 ]

\* A correct process that has not yet sent becomes Byzantine
Faulty(i) ==
  /\ nFaulty < F
  /\ pc[i] \in { "V0", "V1" }
  /\ pc' = [ pc EXCEPT ![i] = "BYZ" ]
  /\ nFaulty' = nFaulty + 1
  /\ UNCHANGED << nSnt0, nSnt1, nRcvd0, nRcvd1 >>

\* A process broadcasts its proposal
Propose(i) ==
  \/ /\ pc[i] = "V0"
     /\ pc' = [ pc EXCEPT ![i] = "S0" ]
     /\ nSnt0' = nSnt0 + 1
     /\ UNCHANGED << nSnt1, nFaulty, nRcvd0, nRcvd1 >>
  \/ /\ pc[i] = "V1"
     /\ pc' = [ pc EXCEPT ![i] = "S1" ]
     /\ nSnt1' = nSnt1 + 1
     /\ UNCHANGED << nSnt0, nFaulty, nRcvd0, nRcvd1 >>

\* A correct process receives a message; Byzantine processes may send
\* both a 0-message and a 1-message
Receive(i) ==
  /\ Correct(i)
  /\ \/ /\ nRcvd0[i] < nSnt0 + nFaulty
        /\ nRcvd0' = [ nRcvd0 EXCEPT ![i] = nRcvd0[i] + 1 ]
        /\ UNCHANGED nRcvd1
     \/ /\ nRcvd1[i] < nSnt1 + nFaulty
        /\ nRcvd1' = [ nRcvd1 EXCEPT ![i] = nRcvd1[i] + 1 ]
        /\ UNCHANGED nRcvd0
  /\ UNCHANGED << nSnt0, nSnt1, nFaulty, pc >>

\* After receiving N - T messages, a process decides or updates its estimate
Decide(i) ==
  /\ pc[i] \in { "S0", "S1" }
  /\ nRcvd0[i] + nRcvd1[i] >= N - T
  /\ \/ /\ nRcvd0[i] >= N - T
        /\ pc' = [ pc EXCEPT ![i] = "D0" ]
     \/ /\ nRcvd1[i] >= N - T
        /\ pc' = [ pc EXCEPT ![i] = "D1" ]
     \/ /\ nRcvd0[i] < N - T
        /\ nRcvd1[i] < N - T
        /\ nRcvd0[i] >= N - 2 * T
        /\ pc' = [ pc EXCEPT ![i] = "U0" ]
     \/ /\ nRcvd0[i] < N - T
        /\ nRcvd1[i] < N - T
        /\ nRcvd1[i] >= N - 2 * T
        /\ pc' = [ pc EXCEPT ![i] = "U1" ]
     \/ /\ nRcvd0[i] < N - 2 * T
        /\ nRcvd1[i] < N - 2 * T
        /\ pc[i] = "S0"
        /\ pc' = [ pc EXCEPT ![i] = "U0" ]
     \/ /\ nRcvd0[i] < N - 2 * T
        /\ nRcvd1[i] < N - 2 * T
        /\ pc[i] = "S1"
        /\ pc' = [ pc EXCEPT ![i] = "U1" ]
  /\ UNCHANGED << nSnt0, nSnt1, nFaulty, nRcvd0, nRcvd1 >>

Step ==
  \E i \in Proc :
    \/ Propose(i)
    \/ Receive(i)
    \/ Decide(i)
    \/ Faulty(i)

Next == Step \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

Spec0 == Init0 /\ [][Next]_vars /\ WF_vars(Step)

Spec1 == Init1 /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------
\* Safety properties

\* If all propose 0, no correct process decides or adopts 1 (use with Spec0)
OneStep0 == \A i \in Proc : pc[i] \notin { "D1", "U1" }

\* If all propose 1, no correct process decides or adopts 0 (use with Spec1)
OneStep1 == \A i \in Proc : pc[i] \notin { "D0", "U0" }

\* Validity for all-0 / all-1 proposals
Validity0 == \A i \in Proc : pc[i] # "D1"
Validity1 == \A i \in Proc : pc[i] # "D0"

\* Agreement: if a correct process decides v, no correct process
\* decides or adopts the other value
Agreement ==
  /\ (\E i \in Proc : pc[i] = "D0") => (\A j \in Proc : pc[j] \notin { "D1", "U1" })
  /\ (\E i \in Proc : pc[i] = "D1") => (\A j \in Proc : pc[j] \notin { "D0", "U0" })

\* Liveness properties

Done(i) == pc[i] \in { "D0", "D1", "U0", "U1", "BYZ" }

\* Every correct process eventually decides or updates its estimate
Termination == <>(\A i \in Proc : Done(i))

\* If all propose 0, all correct processes eventually decide 0 (use with Spec0)
OneStepDecide0 == <>(\A i \in Proc : pc[i] \in { "D0", "BYZ" })

\* If all propose 1, all correct processes eventually decide 1 (use with Spec1)
OneStepDecide1 == <>(\A i \in Proc : pc[i] \in { "D1", "BYZ" })

=============================================================================