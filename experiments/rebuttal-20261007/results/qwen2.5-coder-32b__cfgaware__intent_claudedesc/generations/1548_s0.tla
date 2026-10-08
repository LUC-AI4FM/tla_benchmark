------------------------------- MODULE ByzantineConsensus -------------------------------
VARIABLES values, decisions, sentMessages, receivedMessages, faultyProcesses

CONSTANTS N, T, F

ASSUME /\ N > 3 * T
       /\ F <= T
       /\ F < N

Init == /\ values \in [1..N -> {0, 1}]
        /\ decisions \in [1..N -> {}]
        /\ sentMessages \in [1..N -> {}]
        /\ receivedMessages \in [1..N -> [1..N -> {}]]
        /\ faultyProcesses \in SUBSET (1..N)
        /\ Cardinality(faultyProcesses) <= F

Send == CHOOSE i \in 1..N \ faultyProcesses :
          /\ sentMessages' = [sentMessages EXCEPT ![i] = {values[i]}]
          /\ UNCHANGED <<decisions, receivedMessages, faultyProcesses>>

Receive == CHOOSE i \in 1..N \ faultyProcesses :
             CHOOSE j \in 1..N :
               /\ j \notin faultyProcesses
               /\ values[j] \in sentMessages[j]
               /\ receivedMessages' = [receivedMessages EXCEPT ![i][j] = {values[j]}]
               /\ UNCHANGED <<decisions, sentMessages, faultyProcesses>>

Decide == CHOOSE i \in 1..N \ faultyProcesses :
            LET count0 == Cardinality({j \in 1..N : receivedMessages[i][j] = {0}})
                count1 == Cardinality({j \in 1..N : receivedMessages[i][j] = {1}})
            IN
            /\ (count0 >= N - T) => decisions' = [decisions EXCEPT ![i] = {0}]
            /\ (count1 >= N - T) => decisions' = [decisions EXCEPT ![i] = {1}]
            /\ ~(count0 >= N - T \/ count1 >= N - T) => decisions' = [decisions EXCEPT ![i] = values[i]]
            /\ UNCHANGED <<sentMessages, receivedMessages, faultyProcesses>>

FaultySend == CHOOSE i \in faultyProcesses :
                /\ sentMessages' = [sentMessages EXCEPT ![i] = {0, 1}]
                /\ UNCHANGED <<decisions, receivedMessages, faultyProcesses>>

Next == \/ Send
        \/ Receive
        \/ Decide
        \/ FaultySend

Spec == Init /\ [][Next]_<<values, decisions, sentMessages, receivedMessages, faultyProcesses>>

TypeOK ==
    /\ values \in [1..N -> {0, 1}]
    /\ decisions \in [1..N -> SUBSET {0, 1}]
    /\ sentMessages \in [1..N -> SUBSET {0, 1}]
    /\ receivedMessages \in [1..N -> [1..N -> SUBSET {0, 1}]]
    /\ faultyProcesses \in SUBSET (1..N)

OneStep0_Ltl ==
    \/ \/ /\ decisions = [1..N -> {}]
           /\ sentMessages = [1..N -> {}]
      \/ \/ /\ values = [1..N -> {0}]
             /\ decisions = [1..N -> {0}]

OneStep1_Ltl ==
    \/ \/ /\ decisions = [1..N -> {}]
           /\ sentMessages = [1..N -> {}]
      \/ \/ /\ values = [1..N -> {1}]
             /\ decisions = [1..N -> {1}]

AllDecideOne ==
    \A i \in 1..N : decisions[i] = {1}

WF_Send == WF_vars(Next, <<values, decisions, sentMessages, receivedMessages, faultyProcesses>>, Send)

WF_Receive == WF_vars(Next, <<values, decisions, sentMessages, receivedMessages, faultyProcesses>>, Receive)

WF_Decide == WF_vars(Next, <<values, decisions, sentMessages, receivedMessages, faultyProcesses>>, Decide)

=============================================================================