------------------------------- MODULE DijkstraTokenRing -------------------------------
CONSTANTS N, K

VARIABLES M, pc

ASSUME N > 0 /\ K > N

Init == 
    /\ M \in [0..N-1 -> 0..K-1]
    /\ pc \in [0..N-1 -> {"start"}]

Next ==
    \/ /\ pc[0] = "start"
       /\ M[0] = M[N-1]
       /\ M' = [M EXCEPT ![0] = (M[0] + 1) % K]
       /\ pc' = [pc EXCEPT ![0] = "start"]
    \/ \E i \in 1..N-1 :
         /\ pc[i] = "start"
         /\ M[i] # M[i-1]
         /\ M' = [M EXCEPT ![i] = M[i-1]]
         /\ pc' = [pc EXCEPT ![i] = "start"]

Spec ==
    WF_next(Next) /\
    SpecFair

SpecFair == 
    \A i \in 0..N-1 :
        WF_pc(i, Next)

WF_next(next) ==
    \/ next
    \/ \E i \in 0..N-1 : pc[i] = "start" /\ ~Enabled_i(i)

WF_pc(p, next) ==
    <>[]<>(pc[p] = "start" => <>(next))

Enabled_0 ==
    M[0] = M[N-1]

Enabled_i(i) ==
    i > 0 /\ M[i] # M[i-1]

SomeoneHoldsToken ==
    \E i \in 0..N-1 :
        (i = 0 /\ M[i] = M[N-1]) \/ (i > 0 /\ M[i] # M[i-1])

EventuallyJustOneHoldsToken ==
    <><> (\A j, k \in 0..N-1 : 
            ((j = 0 /\ M[j] = M[N-1]) \/ (j > 0 /\ M[j] # M[j-1])) =>
            (k = 0 /\ M[k] = M[N-1]) \/ (k > 0 /\ M[k] # M[k-1]))

THEOREM Spec => []SomeoneHoldsToken

THEOREM Spec => <>[]EventuallyJustOneHoldsToken
=============================================================================