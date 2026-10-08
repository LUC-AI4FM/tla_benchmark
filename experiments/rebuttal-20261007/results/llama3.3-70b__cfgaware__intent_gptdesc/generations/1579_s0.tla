---------------------------- MODULE TokenCirculation ----------------------------
EXTENDS Integers, TLC

CONSTANT N, K

VARIABLE counters

Init == (* Initialize counters to arbitrary values *)
        /\ counters \in [1..N -> 0..K-1]

Next == (* Asynchronous interleaving of processes *)
        \/ \E i \in 1..N :
            IF i = 1  (* Initiator process *)
            THEN counters' = [counters EXCEPT !i = (counters[i] + 1) % K]
            ELSE counters' = [counters EXCEPT !i = counters[(i - 1) % N]]
        ELSE counters' = counters

Spec == Init /\ [][Next]_

SomeoneHoldsToken == 
        \E i \in 1..N : 
            IF i = 1 
            THEN counters[1] = counters[N]
            ELSE counters[i] # counters[(i - 1) % N]

EventuallyJustOneHoldsToken == 
        <>(\A i \in 1..N : 
            IF i = 1 
            THEN /\ counters[1] = counters[N]
               /\ \A j \in 2..N : counters[j] = counters[(j - 1) % N]
            ELSE /\ counters[i] # counters[(i - 1) % N]
               /\ \A j \in 1..(i-1) + (N-i+1) : 
                   IF j = 1 
                   THEN counters[1] # counters[N]
                   ELSE counters[j] = counters[(j - 1) % N]
        )

THEOREM Spec => []SomeoneHoldsToken
THEOREM Spec => EventuallyJustOneHoldsToken

===============================================================================