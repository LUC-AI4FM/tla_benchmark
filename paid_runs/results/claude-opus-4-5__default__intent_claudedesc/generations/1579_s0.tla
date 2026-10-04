---------------------------- MODULE DijkstraTokenRing ----------------------------
EXTENDS Naturals

CONSTANTS N, K

ASSUME NConstraint == N \in Nat \ {0}
ASSUME KConstraint == K \in Nat /\ K > N

VARIABLES c

vars == <<c>>

Procs == 0..(N-1)

TypeOK == c \in [Procs -> 0..(K-1)]

\* Process 0 holds the token when its value equals the value of process N-1
\* Process i (i > 0) holds the token when its value differs from process i-1
HoldsToken(i) == IF i = 0 
                 THEN c[0] = c[N-1]
                 ELSE c[i] # c[i-1]

\* Count how many processes hold the token
TokenCount == Cardinality({i \in Procs : HoldsToken(i)})

\* Process 0 can act when it holds the token: increment its value mod K
Act0 == /\ c[0] = c[N-1]
        /\ c' = [c EXCEPT ![0] = (c[0] + 1) % K]

\* Process i (i > 0) can act when it holds the token: copy predecessor's value
ActOther(i) == /\ i \in 1..(N-1)
               /\ c[i] # c[i-1]
               /\ c' = [c EXCEPT ![i] = c[i-1]]

Init == c \in [Procs -> 0..(K-1)]

Next == \/ Act0
        \/ \E i \in 1..(N-1) : ActOther(i)

\* Safety: At least one process always holds the token
AtLeastOneToken == \E i \in Procs : HoldsToken(i)

\* Exactly one process holds the token
ExactlyOneToken == TokenCount = 1

\* Liveness: Eventually exactly one process holds the token and it stays that way
\* This is expressed as: eventually always exactly one token
EventuallyStableOneToken == <>[]ExactlyOneToken

\* Fairness: All processes must be scheduled fairly
\* Weak fairness for process 0
Fairness0 == WF_vars(Act0)

\* Weak fairness for all other processes
FairnessOther == \A i \in 1..(N-1) : WF_vars(ActOther(i))

Fairness == Fairness0 /\ FairnessOther

Spec == Init /\ [][Next]_vars /\ Fairness

\* The complete set of properties
Safety == AtLeastOneToken
Liveness == EventuallyStableOneToken

===============================================================================