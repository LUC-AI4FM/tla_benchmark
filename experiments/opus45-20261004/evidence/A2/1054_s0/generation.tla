---------------------------- MODULE EWD426 ----------------------------
EXTENDS Naturals, Integers

CONSTANTS N, M

ASSUME /\ N \in Nat \ {0}
       /\ M \in Nat \ {0}
       /\ N <= M + 1

VARIABLES c

vars == <<c>>

Nodes == 0..(N-1)
Values == 0..(M-1)

TypeOK == c \in [Nodes -> Values]

\* A token exists at position i when all counters before i equal c[0]
\* and all counters from i onward equal (c[0] - 1) mod M
HasToken(i) ==
    IF i = 0
    THEN \A j \in Nodes : c[j] = c[0]
    ELSE /\ \A j \in 0..(i-1) : c[j] = c[0]
         /\ \A j \in i..(N-1) : c[j] = (c[0] - 1 + M) % M

\* Count the number of tokens in the ring
TokenCount == Cardinality({i \in Nodes : HasToken(i)})

\* There is exactly one token in the ring
OneToken == TokenCount = 1

\* Initial state allows any assignment of counter values
Init == c \in [Nodes -> Values]

\* Node 0 creates a token when its counter equals its predecessor's (node N-1)
CreateToken ==
    /\ c[0] = c[N-1]
    /\ c' = [c EXCEPT ![0] = (c[0] + 1) % M]

\* Non-zero node i passes token when its counter differs from predecessor's
PassToken(i) ==
    /\ i \in 1..(N-1)
    /\ c[i] # c[i-1]
    /\ c' = [c EXCEPT ![i] = c[i-1]]

\* Next-state relation
Next ==
    \/ CreateToken
    \/ \E i \in 1..(N-1) : PassToken(i)

\* Temporal specification with weak fairness
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Liveness property: eventually always exactly one token
Stab == <>[]OneToken

\* Helper for TokenCount
RECURSIVE SetCardinality(_)
SetCardinality(S) ==
    IF S = {} THEN 0
    ELSE 1 + SetCardinality(S \ {CHOOSE x \in S : TRUE})

Cardinality(S) == SetCardinality(S)

=======================================================================