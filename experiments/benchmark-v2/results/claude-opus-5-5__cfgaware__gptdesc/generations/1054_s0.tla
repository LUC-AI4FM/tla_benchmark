---------------------------- MODULE EWD426 ----------------------------
(***************************************************************************)
(* Dijkstra's self-stabilizing token ring (EWD426), K-state version.       *)
(* N nodes 0..N-1 arranged in a ring, each holding a counter in 0..M-1.    *)
(* Node 0 holds a token iff its value equals that of node N-1, and moves   *)
(* by setting its value to (c[N-1] + 1) % M.  Node i > 0 holds a token     *)
(* iff its value differs from that of node i-1, and moves by copying the   *)
(* value of node i-1.                                                      *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, M

ASSUME NAssump == N \in Nat /\ N >= 1
ASSUME MAssump == M \in Nat /\ M >= 1
ASSUME NMAssump == N <= M + 1

Node == 0 .. N-1
Val  == 0 .. M-1

VARIABLE c

vars == << c >>

TypeOK == c \in [Node -> Val]

(* Does node i currently hold a token? *)
HasToken(i) ==
    IF i = 0 THEN c[0] = c[N-1]
             ELSE c[i] # c[i-1]

TokenHolders == { i \in Node : HasToken(i) }

UniqueToken == Cardinality(TokenHolders) = 1

Init == c \in [Node -> Val]

CreateToken ==
    /\ HasToken(0)
    /\ c' = [c EXCEPT ![0] = (c[N-1] + 1) % M]

PassToken(i) ==
    /\ i # 0
    /\ HasToken(i)
    /\ c' = [c EXCEPT ![i] = c[i-1]]

Move(i) == IF i = 0 THEN CreateToken ELSE PassToken(i)

Next == \E i \in Node : Move(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* Stabilization: eventually the system reaches and remains in a state    *)
(* with exactly one token.                                                *)
Stab == <>[] UniqueToken

(* Alias for more readable error traces. *)
Alias ==
    [ c      |-> c,
      tokens |-> TokenHolders,
      unique |-> UniqueToken ]

=============================================================================