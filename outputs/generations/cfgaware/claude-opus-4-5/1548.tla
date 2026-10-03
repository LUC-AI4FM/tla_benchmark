---------------------------- MODULE folklore_one_step ----------------------------

EXTENDS Integers, FiniteSets

CONSTANTS N, T, F

VARIABLES nSnt0, nSnt1, nFaulty, nRcvd0, nRcvd1, pc

vars == <<nSnt0, nSnt1, nFaulty, nRcvd0, nRcvd1, pc>>

States == {"V0", "V1", "S0", "S1", "D0", "D1", "U", "BYZ"}

TypeOK ==
    /\ nSnt0 \in 0..N
    /\ nSnt1 \in 0..N
    /\ nFaulty \in 0..F
    /\ nRcvd0 \in [1..N -> 0..N]
    /\ nRcvd1 \in [1..N -> 0..N]
    /\ pc \in [1..N -> States]

Init0 ==
    /\ nSnt0 = 0
    /\ nSnt1 = 0
    /\ nFaulty = 0
    /\ nRcvd0 = [i \in 1..N |-> 0]
    /\ nRcvd1 = [i \in 1..N |-> 0]
    /\ pc = [i \in 1..N |-> "V0"]

Init1 ==
    /\ nSnt0 = 0
    /\ nSnt1 = 0
    /\ nFaulty = 0
    /\ nRcvd0 = [i \in 1..N |-> 0]
    /\ nRcvd1 = [i \in 1..N |-> 0]
    /\ pc = [i \in 1..N |-> "V1"]

Init == Init0 \/ Init1

Propose0(i) ==
    /\ pc[i] = "V0"
    /\ pc' = [pc EXCEPT ![i] = "S0"]
    /\ nSnt0' = nSnt0 + 1
    /\ UNCHANGED <<nSnt1, nFaulty, nRcvd0, nRcvd1>>

Propose1(i) ==
    /\ pc[i] = "V1"
    /\ pc' = [pc EXCEPT ![i] = "S1"]
    /\ nSnt1' = nSnt1 + 1
    /\ UNCHANGED <<nSnt0, nFaulty, nRcvd0, nRcvd1>>

Receive0(i) ==
    /\ pc[i] \in {"S0", "S1"}
    /\ nRcvd0[i] < nSnt0
    /\ nRcvd0' = [nRcvd0 EXCEPT ![i] = nRcvd0[i] + 1]
    /\ UNCHANGED <<nSnt0, nSnt1, nFaulty, nRcvd1, pc>>

Receive1(i) ==
    /\ pc[i] \in {"S0", "S1"}
    /\ nRcvd1[i] < nSnt1
    /\ nRcvd1' = [nRcvd1 EXCEPT ![i] = nRcvd1[i] + 1]
    /\ UNCHANGED <<nSnt0, nSnt1, nFaulty, nRcvd0, pc>>

ReceiveByz0(i) ==
    /\ pc[i] \in {"S0", "S1"}
    /\ nRcvd0[i] < nSnt0 + nFaulty
    /\ nRcvd0' = [nRcvd0 EXCEPT ![i] = nRcvd0[i] + 1]
    /\ UNCHANGED <<nSnt0, nSnt1, nFaulty, nRcvd1, pc>>

ReceiveByz1(i) ==
    /\ pc[i] \in {"S0", "S1"}
    /\ nRcvd1[i] < nSnt1 + nFaulty
    /\ nRcvd1' = [nRcvd1 EXCEPT ![i] = nRcvd1[i] + 1]
    /\ UNCHANGED <<nSnt0, nSnt1, nFaulty, nRcvd0, pc>>

Decide0(i) ==
    /\ pc[i] \in {"S0", "S1"}
    /\ nRcvd0[i] >= N - T
    /\ nRcvd1[i] <= T
    /\ pc' = [pc EXCEPT ![i] = "D0"]
    /\ UNCHANGED <<nSnt0, nSnt1, nFaulty, nRcvd0, nRcvd1>>

Decide1(i) ==
    /\ pc[i] \in {"S0", "S1"}
    /\ nRcvd1[i] >= N - T
    /\ nRcvd0[i] <= T
    /\ pc' = [pc EXCEPT ![i] = "D1"]
    /\ UNCHANGED <<nSnt0, nSnt1, nFaulty, nRcvd0, nRcvd1>>

DecideUndecided(i) ==
    /\ pc[i] \in {"S0", "S1"}
    /\ nRcvd0[i] + nRcvd1[i] >= N - T
    /\ nRcvd0[i] < N - T
    /\ nRcvd1[i] < N - T
    /\ pc' = [pc EXCEPT ![i] = "U"]
    /\ UNCHANGED <<nSnt0, nSnt1, nFaulty, nRcvd0, nRcvd1>>

BecomeFaulty(i) ==
    /\ pc[i] \notin {"BYZ", "D0", "D1", "U"}
    /\ nFaulty < F
    /\ nFaulty' = nFaulty + 1
    /\ pc' = [pc EXCEPT ![i] = "BYZ"]
    /\ UNCHANGED <<nSnt0, nSnt1, nRcvd0, nRcvd1>>

Step(i) ==
    \/ Propose0(i)
    \/ Propose1(i)
    \/ Receive0(i)
    \/ Receive1(i)
    \/ ReceiveByz0(i)
    \/ ReceiveByz1(i)
    \/ Decide0(i)
    \/ Decide1(i)
    \/ DecideUndecided(i)
    \/ BecomeFaulty(i)

Next == \E i \in 1..N : Step(i)

Fairness == \A i \in 1..N : WF_vars(Step(i))

Spec == Init /\ [][Next]_vars /\ Fairness

Agreement ==
    \A i, j \in 1..N :
        (pc[i] \in {"D0", "D1"} /\ pc[j] \in {"D0", "D1"}) =>
            (pc[i] = pc[j])

Validity0 ==
    (\A i \in 1..N : pc[i] \in {"V0", "S0", "D0", "BYZ"}) =>
        (\A i \in 1..N : pc[i] \notin {"D1"})

Validity1 ==
    (\A i \in 1..N : pc[i] \in {"V1", "S1", "D1", "BYZ"}) =>
        (\A i \in 1..N : pc[i] \notin {"D0"})

AllDecideZero ==
    \A i \in 1..N : pc[i] \in {"D0", "BYZ"}

AllDecideOne ==
    \A i \in 1..N : pc[i] \in {"D1", "BYZ"}

OneStep0_Ltl ==
    ((\A i \in 1..N : pc[i] = "V0") /\ nFaulty = 0) => <>AllDecideZero

OneStep1_Ltl ==
    ((\A i \in 1..N : pc[i] = "V1") /\ nFaulty = 0) => <>AllDecideOne

=============================================================================