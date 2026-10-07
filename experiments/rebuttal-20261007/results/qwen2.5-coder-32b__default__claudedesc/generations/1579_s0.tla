------------------------------- MODULE DijkstraTokenRing -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, K
ASSUME N > 0 /\ K > N

VARIABLES M, pc

Init == 
    /\ M \in [0..N-1 -> 0..K-1]
    /\ pc \in [0..N-1 -> {"start", "increment", "copy"}]

Next ==
    \/ /\ pc[0] = "start"
       /\ M[0] = M[N-1]
       /\ pc' = [pc EXCEPT ![0] = "increment"]
       /\ M' = [M EXCEPT ![0] = (M[0] + 1) % K]
       /\ \A i \in 1..N-1: pc'[i] = pc[i]
    \/ /\ \E i \in 1..N-1: pc[i] = "start" /\ M[i] # M[i-1]
       /\ pc' = [pc EXCEPT ![i] = "copy"]
       /\ M' = [M EXCEPT ![i] = M[i-1]]
       /\ \A j \in 0..N-1 \ {i}: pc'[j] = pc[j]

Spec ==
    /\ Init
    /\ [][Next]_<<pc>>
    /\ WF_next(<<pc>>)

SomeoneHoldsToken ==
    \/ M[0] = M[N-1]
    \/ \E i \in 1..N-1: M[i] # M[i-1]

EventuallyJustOneHoldsToken ==
    <>[](\A i \in 0..N-1: (\E j \in 0..N-1: (i = j <-> (j = 0 /\ M[0] = M[N-1]) \/ (j > 0 /\ M[j] # M[j-1]))))

THEOREM Spec => []SomeoneHoldsToken
THEOREM Spec => <>[]EventuallyJustOneHoldsToken

=============================================================================