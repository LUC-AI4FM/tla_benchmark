---------------------------- MODULE TokenRing ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, K

ASSUME NAssumption == N \in Nat \ {0}
ASSUME KAssumption == K \in Nat /\ K > N

Procs  == 0..(N-1)
Values == 0..(K-1)

VARIABLES c

vars == << c >>

TypeOK == c \in [Procs -> Values]

\* Any initial configuration is allowed (self-stabilization).
Init == c \in [Procs -> Values]

\* Process i holds the token.
TokenAt(i) ==
    IF i = 0 THEN c[0] = c[N-1]
             ELSE c[i] # c[i-1]

Holders == { i \in Procs : TokenAt(i) }

TokenCount == Cardinality(Holders)

\* The initiator (process 0) passes the token by incrementing its counter.
CreateToken ==
    /\ c[0] = c[N-1]
    /\ c' = [c EXCEPT ![0] = (c[N-1] + 1) % K]

\* Other processes pass the token by copying the predecessor's counter.
PassToken(i) ==
    /\ i \in 1..(N-1)
    /\ c[i] # c[i-1]
    /\ c' = [c EXCEPT ![i] = c[i-1]]

Next == CreateToken \/ \E i \in 1..(N-1) : PassToken(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Safety: at least one process always holds the token.
SomeoneHoldsToken == \E i \in Procs : TokenAt(i)

\* Exactly one process holds the token.
SingleToken ==
    \E i \in Procs : /\ TokenAt(i)
                     /\ \A j \in Procs : TokenAt(j) => j = i

\* The possible numbers of token holders in any reachable state.
PossibleCounts == 1..N

_POSSIBLE == /\ TypeOK
             /\ TokenCount \in PossibleCounts

\* Liveness: token-passing steps keep occurring.
TokenPasses == []<><<Next>>_vars

\* Convergence: eventually always exactly one token holder.
EventuallyJustOneHoldsToken == <>[]SingleToken

=============================================================================