---------------------------- MODULE EWD426 ----------------------------
EXTENDS Naturals

CONSTANTS N, M

ASSUME NAssumption == N \in Nat \ {0}
ASSUME MAssumption == M \in Nat \ {0}
ASSUME NMAssumption == N <= M + 1

VARIABLES c

vars == <<c>>

Nodes == 0 .. N-1
Values == 0 .. M-1

TypeOK == c \in [Nodes -> Values]

\* A token exists at position i when all counters before i equal c[0]
\* and all counters from i onward equal (c[0] - 1) mod M
HasToken(i) ==
    IF i = 0
    THEN c[0] # c[N-1]
    ELSE c[i] # c[i-1]

TokenCount == Cardinality({i \in Nodes : HasToken(i)})

\* Alternative definition: count tokens by checking the implicit token definition
\* A unique token exists when the system is in a legitimate state
UniqueToken ==
    \E i \in Nodes :
        /\ \A j \in 0 .. i-1 : c[j] = c[0]
        /\ \A j \in i .. N-1 : c[j] = (c[0] + M - 1) % M
        /\ i > 0

\* Node 0 has the token when its value equals its predecessor (N-1)
Node0HasToken == c[0] = c[N-1]

\* Count the number of tokens based on discontinuities
NumTokens ==
    LET count == Cardinality({i \in 1 .. N-1 : c[i] # c[i-1]})
    IN IF c[0] = c[N-1] THEN count ELSE count + 1

\* Exactly one token exists in the ring
OneToken == NumTokens = 1

\* Initial state: any assignment of counter values
Init == c \in [Nodes -> Values]

\* CreateToken: enabled when node 0's counter equals node N-1's counter
\* Increments c[0] modulo M
CreateToken ==
    /\ c[0] = c[N-1]
    /\ c' = [c EXCEPT ![0] = (c[0] + 1) % M]

\* PassToken(i): enabled for non-zero node i when its counter differs from predecessor
\* Copies the predecessor's value
PassToken(i) ==
    /\ i \in 1 .. N-1
    /\ c[i] # c[i-1]
    /\ c' = [c EXCEPT ![i] = c[i-1]]

\* Next state relation: disjunction of all actions
Next ==
    \/ CreateToken
    \/ \E i \in 1 .. N-1 : PassToken(i)

\* Temporal specification with weak fairness
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Liveness property: eventually always exactly one token
Stab == <>[]OneToken

\* For Cardinality
LOCAL INSTANCE FiniteSets

=======================================================================