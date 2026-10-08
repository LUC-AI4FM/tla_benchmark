------------------------------- MODULE TokenRing -------------------------------

CONSTANTS N, K

ASSUME N > 0 /\ K > N

VARIABLES values

Init == /\ values \in [0..N-1 -> 0..K-1]
        /\ values[0] = 0

Next ==
    \/ /\ values[0] = values[N-1]
       /\ values' = [values EXCEPT ![0] = (values[0] + 1) % K]
    \/ \E i \in 1..N-1 : 
         /\ values[i] # values[i-1]
         /\ values' = [values EXCEPT ![i] = values[i-1]]

Spec == Init /\ [][Next]_<<values>>

SomeoneHoldsToken ==
    \/ values[0] = values[N-1]
    \/ \E i \in 1..N-1 : values[i] # values[i-1]

EventuallyJustOneHoldsToken ==
    <>[] (\A j, k \in 0..N-1 : j # k => (values[j] = values[j-1] \/ values[k] = values[k-1]))

Fairness == WF_next(Next)

THEOREM Spec => []<>SomeoneHoldsToken

THEOREM Spec => Fairness /\ []<>EventuallyJustOneHoldsToken

=============================================================================