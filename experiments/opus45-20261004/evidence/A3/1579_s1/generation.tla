---------------------------- MODULE DijkstraTokenRing ----------------------------
EXTENDS Naturals, TLAPS

CONSTANT N, K

ASSUME NPositive == N > 0
ASSUME KGreaterThanN == K > N

VARIABLES x

vars == <<x>>

TypeOK == x \in [0..(N-1) -> 0..(K-1)]

HasToken(i) ==
    IF i = 0
    THEN x[i] = x[N-1]
    ELSE x[i] # x[i-1]

TokenCount == Cardinality({i \in 0..(N-1) : HasToken(i)})

Cardinality(S) == 
    LET Card[T \in SUBSET S] == 
        IF T = {} THEN 0
        ELSE 1 + Card[T \ {CHOOSE t \in T : TRUE}]
    IN Card[S]

System(i) ==
    /\ HasToken(i)
    /\ IF i = 0
       THEN x' = [x EXCEPT ![0] = (x[0] + 1) % K]
       ELSE x' = [x EXCEPT ![i] = x[i-1]]

Proc(i) == System(i)

Init == x \in [0..(N-1) -> 0..(K-1)]

Next == \E i \in 0..(N-1) : Proc(i)

Fairness == \A i \in 0..(N-1) : WF_vars(Proc(i))

Spec == Init /\ [][Next]_vars /\ Fairness

AtLeastOneToken == \E i \in 0..(N-1) : HasToken(i)

ExactlyOneToken == 
    \E i \in 0..(N-1) : 
        /\ HasToken(i)
        /\ \A j \in 0..(N-1) : j # i => ~HasToken(j)

Legitimate == ExactlyOneToken

Safety == []AtLeastOneToken

Liveness == <>[]ExactlyOneToken

Convergence == <>Legitimate

THEOREM TypeCorrect == Spec => []TypeOK
PROOF OMITTED

THEOREM AlwaysSomeToken == Spec => []AtLeastOneToken
PROOF OMITTED

THEOREM EventuallyOneToken == Spec => <>[]ExactlyOneToken
PROOF OMITTED

=================================================================================