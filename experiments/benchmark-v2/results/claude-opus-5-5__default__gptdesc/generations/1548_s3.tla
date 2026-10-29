---------------------------- MODULE cf1s ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES nSnt0,    \* number of VALUE 0 messages sent by correct processes
          nSnt1,    \* number of VALUE 1 messages sent by correct processes
          nFaulty,  \* number of processes that have become Byzantine
          pc,       \* control state of every process
          nRcvd0,   \* number of 0-messages received by each process
          nRcvd1    \* number of 1-messages received by each process

ASSUME NTF == /\ N \in Nat /\ T \in Nat /\ F \in Nat
              /\ N > 3 * T
              /\ T >= F
              /\ F >= 0

Proc == 1 .. N

Status == { "V0", "V1", "S0", "S1", "D0", "D1", "U0", "U1", "BYZ" }

vars == << nSnt0, nSnt1, nFaulty, pc, nRcvd0, nRcvd1 >>

TypeOK ==
  /\ nSnt0 \in 0 .. N
  /\ nSnt1 \in 0 .. N
  /\ nFaulty \in 0 .. F
  /\ pc \in [ Proc -> Status ]
  /\ nRcvd0 \in [ Proc -> 0 .. N ]
  /\ nRcvd1 \in [ Proc -> 0 .. N ]

Init ==
  /\ nSnt0 = 0
  /\ nSnt1 = 0
  /\ nFaulty = 0
  /\ pc \in [ Proc -> { "V0", "V1" } ]
  /\ nRcvd0 = [ i \in Proc |-> 0 ]
  /\ nRcvd1 = [ i \in Proc |-> 0 ]

\* All correct processes propose 0
Init0 ==
  /\ nSnt0 = 0
  /\ nSnt1 = 0
  /\ nFaulty = 0
  /\ pc = [ i \in Proc |-> "V0" ]
  /\ nRcvd0 = [ i \in Proc |-> 0 ]
  /\ nRcvd1 = [ i \in Proc |-> 0 ]

\* All correct processes propose 1
Init1 ==
  /\ nSnt0 = 0
  /\ nSnt1 = 0
  /\ nFaulty = 0
  /\ pc = [ i \in Proc |-> "V1" ]
  /\ nRcvd0 = [ i \in Proc |-> 0 ]
  /\ nRcvd1 = [ i \in Proc |-> 0 ]

\* A correct process becomes Byzantine
Faulty(i) ==
  /\ nFaulty < F
  /\ pc[i] # "BYZ"
  /\ pc' = [ pc EXCEPT ![i] = "BYZ" ]
  /\ nFaulty' = nFaulty + 1
  /\ UNCHANGED << nSnt0, nSnt1, nRcvd0, nRcvd1 >>

\* A correct process broadcasts its proposal
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
\* both values, hence the bound nSntX + nFaulty
Receive(i) ==
  /\ pc[i] # "BYZ"
  /\ \/ /\ nRcvd0[i] < nSnt0 + nFaulty
        /\ nRcvd0' = [ nRcvd0 EXCEPT ![i] = nRcvd0[i] + 1 ]
        /\ UNCHANGED << nSnt0, nSnt1, nFaulty, pc, nRcvd1 >>
     \/ /\ nRcvd1[i] < nSnt1 + nFaulty
        /\ nRcvd1' = [ nRcvd1 EXCEPT ![i] = nRcvd1[i] + 1 ]
        /\ UNCHANGED << nSnt0, nSnt1, nFaulty, pc, nRcvd0 >>

\* After receiving N - T messages, a process either decides or updates
\* its estimate (underlying consensus fallback)
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
        /\ pc' = [ pc EXCEPT ![i] = IF pc[i] = "S0" THEN "U0" ELSE "U1" ]
  /\ UNCHANGED << nSnt0, nSnt1, nFaulty, nRcvd0, nRcvd1 >>

Step(i) ==
  \/ Propose(i)
  \/ Receive(i)
  \/ Decide(i)

Next ==
  \/ \E i \in Proc : Step(i)
  \/ \E i \in Proc : Faulty(i)
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(\E i \in Proc : Step(i))

Spec0 == Init0 /\ [][Next]_vars /\ WF_vars(\E i \in Proc : Step(i))

Spec1 == Init1 /\ [][Next]_vars /\ WF_vars(\E i \in Proc : Step(i))

\* ---------------- Safety ----------------

\* No two correct processes decide differently
Agreement ==
  \A i, j \in Proc :
    ~(pc[i] = "D0" /\ pc[j] = "D1")

\* A correct process deciding v forces others not to adopt the other value
AgreementWithEstimate ==
  \A i, j \in Proc :
    /\ (pc[i] = "D0" => pc[j] # "U1")
    /\ (pc[i] = "D1" => pc[j] # "U0")

\* Validity: if all propose 0, no one decides 1 or adopts 1 (and vice versa)
Validity0 ==
  (\A i \in Proc : pc[i] = "V0")
    => [](\A i \in Proc : pc[i] # "D1" /\ pc[i] # "U1")

Validity1 ==
  (\A i \in Proc : pc[i] = "V1")
    => [](\A i \in Proc : pc[i] # "D0" /\ pc[i] # "U0")

\* ---------------- Liveness ----------------

\* One-step decision: if all correct propose the same value, they all decide it
OneStep0 ==
  (\A i \in Proc : pc[i] = "V0")
    => <>(\A i \in Proc : pc[i] = "D0" \/ pc[i] = "BYZ")

OneStep1 ==
  (\A i \in Proc : pc[i] = "V1")
    => <>(\A i \in Proc : pc[i] = "D1" \/ pc[i] = "BYZ")

\* Termination: every correct process eventually decides or adopts an estimate
Termination ==
  <>(\A i \in Proc : pc[i] \in { "D0", "D1", "U0", "U1", "BYZ" })

=============================================================================