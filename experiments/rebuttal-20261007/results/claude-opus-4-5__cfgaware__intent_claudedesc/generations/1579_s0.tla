---------------------------- MODULE DijkstraTokenRing ----------------------------

EXTENDS Naturals

CONSTANTS N, K

ASSUME K > N /\ N > 0

VARIABLES c

vars == <<c>>

TypeOK == c \in [0..N-1 -> 0..K-1]

Init == c \in [0..N-1 -> 0..K-1]

Process0Enabled == c[0] = c[N-1]

ProcessIEnabled(i) == c[i] # c[i-1]

Process0 == 
    /\ Process0Enabled
    /\ c' = [c EXCEPT ![0] = (c[0] + 1) % K]

ProcessI(i) ==
    /\ i \in 1..N-1
    /\ ProcessIEnabled(i)
    /\ c' = [c EXCEPT ![i] = c[i-1]]

Next == 
    \/ Process0
    \/ \E i \in 1..N-1 : ProcessI(i)

Fairness ==
    /\ WF_vars(Process0)
    /\ \A i \in 1..N-1 : WF_vars(ProcessI(i))

Spec == Init /\ [][Next]_vars /\ Fairness

HoldsToken(i) ==
    IF i = 0 
    THEN c[0] = c[N-1]
    ELSE c[i] # c[i-1]

TokenCount == Cardinality({i \in 0..N-1 : HoldsToken(i)})

RECURSIVE CardinalityRec(_)
CardinalityRec(S) ==
    IF S = {} THEN 0
    ELSE 1 + CardinalityRec(S \ {CHOOSE x \in S : TRUE})

Cardinality(S) == CardinalityRec(S)

SomeoneHoldsToken == \E i \in 0..N-1 : HoldsToken(i)

ExactlyOneHoldsToken == TokenCount = 1

EventuallyJustOneHoldsToken == <>[](ExactlyOneHoldsToken)

=============================================================================