---------------------------- MODULE EWD426 ----------------------------
EXTENDS Naturals

CONSTANTS N, M

ASSUME NMConstraint == N <= M + 1 /\ N > 0 /\ M > 0

VARIABLES counter

vars == <<counter>>

Nodes == 0..(N-1)

TypeOK == counter \in [Nodes -> 0..(M-1)]

Pred(i) == IF i = 0 THEN N - 1 ELSE i - 1

IsPrivileged(i) ==
    IF i = 0
    THEN counter[0] = counter[N-1]
    ELSE counter[i] # counter[Pred(i)]

HasToken(i) == IsPrivileged(i)

TokenCount == Cardinality({i \in Nodes : HasToken(i)})

Cardinality(S) == 
    LET Card[T \in SUBSET Nodes] == 
        IF T = {} THEN 0
        ELSE 1 + Card[T \ {CHOOSE x \in T : TRUE}]
    IN Card[S]

ExactlyOneToken == TokenCount = 1

Init == counter \in [Nodes -> 0..(M-1)]

Node0Action ==
    /\ counter[0] = counter[N-1]
    /\ counter' = [counter EXCEPT ![0] = (counter[0] + 1) % M]

NodeIAction(i) ==
    /\ i # 0
    /\ counter[i] # counter[Pred(i)]
    /\ counter' = [counter EXCEPT ![i] = counter[Pred(i)]]

Next ==
    \/ Node0Action
    \/ \E i \in 1..(N-1) : NodeIAction(i)

Fairness ==
    /\ WF_vars(Node0Action)
    /\ \A i \in 1..(N-1) : WF_vars(NodeIAction(i))

Spec == Init /\ [][Next]_vars /\ Fairness

Stabilization == <>[]ExactlyOneToken

=======================================================================