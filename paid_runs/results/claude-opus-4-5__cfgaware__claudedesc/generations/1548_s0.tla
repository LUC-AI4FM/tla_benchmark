---------------------------- MODULE OneStepConsensus ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F

ASSUME N > 3 * T /\ 3 * T >= 3 * F /\ F >= 0

VARIABLES
    pc,          \* pc[i] is the program counter of process i
    nSnt0,       \* number of 0-messages sent by correct processes
    nSnt1,       \* number of 1-messages sent by correct processes
    nSnt0F,      \* number of 0-messages injected by faulty processes
    nSnt1F,      \* number of 1-messages injected by faulty processes
    nRcvd0,      \* nRcvd0[i] is number of 0-messages received by process i
    nRcvd1,      \* nRcvd1[i] is number of 1-messages received by process i
    nFaulty      \* number of faulty processes

Procs == 1..N

Status == {"V0", "V1", "S0", "S1", "D0", "D1", "U0", "U1", "BYZ"}

vars == <<pc, nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty>>

TypeOK ==
    /\ pc \in [Procs -> Status]
    /\ nSnt0 \in 0..N
    /\ nSnt1 \in 0..N
    /\ nSnt0F \in 0..N
    /\ nSnt1F \in 0..N
    /\ nRcvd0 \in [Procs -> 0..(2*N)]
    /\ nRcvd1 \in [Procs -> 0..(2*N)]
    /\ nFaulty \in 0..F

Init ==
    /\ pc \in [Procs -> {"V0", "V1"}]
    /\ nSnt0 = 0
    /\ nSnt1 = 0
    /\ nSnt0F = 0
    /\ nSnt1F = 0
    /\ nRcvd0 = [i \in Procs |-> 0]
    /\ nRcvd1 = [i \in Procs |-> 0]
    /\ nFaulty = 0

\* A process proposes its initial value by broadcasting and moving to sent state
Propose(i) ==
    /\ pc[i] \in {"V0", "V1"}
    /\ IF pc[i] = "V0"
       THEN /\ pc' = [pc EXCEPT ![i] = "S0"]
            /\ nSnt0' = nSnt0 + 1
            /\ UNCHANGED nSnt1
       ELSE /\ pc' = [pc EXCEPT ![i] = "S1"]
            /\ nSnt1' = nSnt1 + 1
            /\ UNCHANGED nSnt0
    /\ UNCHANGED <<nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty>>

\* A process receives messages (increments counters up to sent totals)
Receive(i) ==
    /\ pc[i] \notin {"BYZ", "D0", "D1"}
    /\ \/ /\ nRcvd0[i] < nSnt0 + nSnt0F
          /\ nRcvd0' = [nRcvd0 EXCEPT ![i] = nRcvd0[i] + 1]
          /\ UNCHANGED nRcvd1
       \/ /\ nRcvd1[i] < nSnt1 + nSnt1F
          /\ nRcvd1' = [nRcvd1 EXCEPT ![i] = nRcvd1[i] + 1]
          /\ UNCHANGED nRcvd0
    /\ UNCHANGED <<pc, nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty>>

\* A process in sent state decides when it has received enough messages
Decide(i) ==
    /\ pc[i] \in {"S0", "S1"}
    /\ nRcvd0[i] + nRcvd1[i] >= N - T
    /\ IF nRcvd0[i] >= N - T
       THEN pc' = [pc EXCEPT ![i] = "D0"]
       ELSE IF nRcvd1[i] >= N - T
            THEN pc' = [pc EXCEPT ![i] = "D1"]
            ELSE IF pc[i] = "S0"
                 THEN pc' = [pc EXCEPT ![i] = "U0"]
                 ELSE pc' = [pc EXCEPT ![i] = "U1"]
    /\ UNCHANGED <<nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty>>

\* A correct process becomes Byzantine (faulty)
Faulty(i) ==
    /\ pc[i] \notin {"BYZ"}
    /\ nFaulty < F
    /\ pc' = [pc EXCEPT ![i] = "BYZ"]
    /\ nFaulty' = nFaulty + 1
    \* Faulty process can inject arbitrary messages
    /\ \E d0, d1 \in 0..1 :
        /\ nSnt0F' = nSnt0F + d0
        /\ nSnt1F' = nSnt1F + d1
    /\ UNCHANGED <<nSnt0, nSnt1, nRcvd0, nRcvd1>>

\* Byzantine processes can inject additional messages at any time
ByzantineInject ==
    /\ nFaulty > 0
    /\ \/ /\ nSnt0F < nFaulty
          /\ nSnt0F' = nSnt0F + 1
          /\ UNCHANGED nSnt1F
       \/ /\ nSnt1F < nFaulty
          /\ nSnt1F' = nSnt1F + 1
          /\ UNCHANGED nSnt0F
    /\ UNCHANGED <<pc, nSnt0, nSnt1, nRcvd0, nRcvd1, nFaulty>>

Next ==
    \/ \E i \in Procs : Propose(i)
    \/ \E i \in Procs : Receive(i)
    \/ \E i \in Procs : Decide(i)
    \/ \E i \in Procs : Faulty(i)
    \/ ByzantineInject

\* Actions for fairness
ProposeAction == \E i \in Procs : Propose(i)
ReceiveAction == \E i \in Procs : Receive(i)
DecideAction == \E i \in Procs : Decide(i)

Fairness ==
    /\ WF_vars(ProposeAction)
    /\ WF_vars(ReceiveAction)
    /\ WF_vars(DecideAction)

Spec == Init /\ [][Next]_vars /\ Fairness

\* All processes initially propose 0
AllInitial0 == \A i \in Procs : pc[i] = "V0"

\* All processes initially propose 1
AllInitial1 == \A i \in Procs : pc[i] = "V1"

\* No process is in U0, U1, or D1 state
NoUorD1 == \A i \in Procs : pc[i] \notin {"U0", "U1", "D1"}

\* No process is in U0, U1, or D0 state
NoUorD0 == \A i \in Procs : pc[i] \notin {"U0", "U1", "D0"}

\* If all processes initially propose 0, they never reach U or D1 states
OneStep0_Ltl == AllInitial0 => []NoUorD1

\* If all processes initially propose 1, they eventually all leave U and D0 states
OneStep1_Ltl == AllInitial1 => <>NoUorD0

\* Every process eventually decides D1
AllDecideOne == <>(\A i \in Procs : pc[i] = "D1")

=============================================================================