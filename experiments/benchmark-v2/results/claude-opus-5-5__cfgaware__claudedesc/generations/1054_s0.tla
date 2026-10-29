------------------------------ MODULE TokenRing ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, M

ASSUME NMAssumption == /\ N \in Nat \ {0}
                       /\ M \in Nat \ {0}
                       /\ N <= M + 1

Node == 0 .. N-1
Value == 0 .. M-1

VARIABLE c

vars == << c >>

Pred(i) == IF i = 0 THEN N-1 ELSE i-1

TypeOK == c \in [Node -> Value]

HasToken(i) == IF i = 0 THEN c[0] = c[N-1]
                        ELSE c[i] # c[i-1]

Init == c \in [Node -> Value]

CreateToken ==
    /\ c[0] = c[N-1]
    /\ c' = [c EXCEPT ![0] = (c[N-1] + 1) % M]

PassToken(i) ==
    /\ i # 0
    /\ c[i] # c[i-1]
    /\ c' = [c EXCEPT ![i] = c[i-1]]

Next == CreateToken \/ \E i \in Node \ {0} : PassToken(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

UniqueToken ==
    \E i \in 0 .. N :
        c = [j \in Node |-> IF j < i THEN c[0] ELSE (c[0] - 1) % M]

Stab == <>[]UniqueToken

Alias == [ c |-> c,
           tokens |-> { i \in Node : HasToken(i) },
           unique |-> UniqueToken ]

=============================================================================