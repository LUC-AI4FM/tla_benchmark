MODULE OneStepConsensus
EXTENDS Integers, TLC

CONSTANTS N, F, T

ASSUME N > 0 /\ F <= N /\ T <= N

Nat == {n \in Int : n >= 0}

VARIABLES proposed, msg, decided, faultySet, sentCount, recvCount

Init ==
    /\ proposed \in [1..N -> 0 \/ 1]
    /\ (proposed = [i \in 1..N |-> 0] \/ proposed = [i \in 1..N |-> 1])
    /\ msg = [i \in 1..N |-> [j \in 1..N |-> 0]]
    /\ decided = [i \in 1..N |-> "undecided"]
    /\ faultySet = {}
    /\ sentCount = [i \in 1..N |-> 0]
    /\ recvCount = [i \in 1..N |-> 0]

SendStep ==
    /\ msg' = [i \in 1..N |-> [j \in 1..N |-> IF i \in faultySet THEN CHOOSE v \in {0,1} : TRUE ELSE proposed[i]]]
    /\ sentCount' = [i \in 1..N |-> sentCount[i] + N]
    /\ recvCount' = [i \in 1..N |-> recvCount[i] + N]
    /\ UNCHANGED <<proposed, decided, faultySet>>

DecideStep ==
    /\ decided' =
        [i \in 1..N |-> IF i \notin faultySet THEN
                LET count0 == \# {j \in 1..N : msg[j][i] = 0}
                    count1 == \# {j \in 1..N : msg[j][i] = 1} IN
                  IF count