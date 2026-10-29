---------------------------- MODULE APTokenRing ----------------------------
(***************************************************************************)
(* Wrapper that supplies Apalache type annotations for the TokenRing       *)
(* specification (Dijkstra's self-stabilizing token ring, EWD 426).        *)
(* The TokenRing definitions are given inline so that this module is       *)
(* self-contained and parses on its own.                                   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    \* @type: Int;
    N,
    \* @type: Int;
    M

ASSUME NAssumption == N \in Nat \ {0}
ASSUME MAssumption == M \in Nat \ {0}

VARIABLES
    \* @type: Int -> Int;
    c

vars == << c >>

Node  == 0 .. N-1
Value == 0 .. M-1

TypeOK == c \in [Node -> Value]

Init == c \in [Node -> Value]

\* Node 0 holds a token when its value equals that of its predecessor N-1.
\* Any other node i holds a token when its value differs from node i-1.
HasToken(i) ==
    IF i = 0 THEN c[0] = c[N-1] ELSE c[i] # c[i-1]

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

TokensHeld == { i \in Node : HasToken(i) }

UniqueToken == Cardinality(TokensHeld) = 1

AtLeastOneToken == TokensHeld # {}

Stabilization == <>[]UniqueToken

=============================================================================