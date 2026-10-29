---------------------------- MODULE APTokenRing ----------------------------
EXTENDS Naturals

CONSTANTS
    \* @type: Int;
    N,
    \* @type: Int;
    M

VARIABLES
    \* @type: Int -> Int;
    c

vars == << c >>

Node == 0 .. N-1

Values == 0 .. M-1

TypeOK == c \in [Node -> Values]

Init == c \in [Node -> Values]

\* Node 0 holds the token when its counter equals that of its predecessor (N-1)
HasToken(i) ==
    IF i = 0 THEN c[0] = c[N-1]
             ELSE c[i] # c[i-1]

CreateToken ==
    /\ c[0] = c[N-1]
    /\ c' = [c EXCEPT ![0] = (c[N-1] + 1) % M]

PassToken(i) ==
    /\ i # 0
    /\ c[i] # c[i-1]
    /\ c' = [c EXCEPT ![i] = c[i-1]]

Next ==
    \/ CreateToken
    \/ \E i \in Node \ {0} : PassToken(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

UniqueToken == \E i \in Node : \A j \in Node : HasToken(j) <=> (i = j)

Stab == <>[]UniqueToken

=============================================================================