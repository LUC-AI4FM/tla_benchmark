------------------------------- MODULE EWD426 -------------------------------
(***************************************************************************)
(* Dijkstra's self-stabilizing token ring algorithm (EWD426).              *)
(* N nodes in a ring, each with a counter in 0..M-1.                       *)
(* Node 0 holds a token iff its value equals that of node N-1, and it      *)
(* moves by incrementing (mod M) relative to node N-1.                     *)
(* Node i > 0 holds a token iff its value differs from node i-1, and it    *)
(* moves by copying the value of node i-1.                                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, M

ASSUME NAssump  == N \in Nat \ {0}
ASSUME MAssump  == M \in Nat \ {0}
ASSUME RingAssump == N <= M + 1

Node   == 0 .. N-1
Values == 0 .. M-1

VARIABLE c

vars == << c >>

TypeOK == c \in [Node -> Values]

(* Token predicate for each node *)
HasToken(i) ==
    IF i = 0 THEN c[0] = c[N-1]
             ELSE c[i] # c[i-1]

TokenHolders == { i \in Node : HasToken(i) }

UniqueToken == \E i \in Node : TokenHolders = {i}

(* Arbitrary initial state: the algorithm is self-stabilizing *)
Init == c \in [Node -> Values]

(* Node 0 creates a new token *)
CreateToken ==
    /\ c[0] = c[N-1]
    /\ c' = [c EXCEPT ![0] = (c[N-1] + 1) % M]

(* Node i > 0 passes the token by copying its predecessor *)
PassToken(i) ==
    /\ i # 0
    /\ c[i] # c[i-1]
    /\ c' = [c EXCEPT ![i] = c[i-1]]

Next ==
    \/ CreateToken
    \/ \E i \in Node \ {0} : PassToken(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

(* There is always at least one token, so the system never deadlocks *)
AtLeastOneToken == TokenHolders # {}

(* Self-stabilization: eventually the system reaches, and remains in,    *)
(* a state with exactly one token.                                         *)
Stabilization == <>[]UniqueToken

THEOREM Spec => []TypeOK
THEOREM Spec => []AtLeastOneToken
THEOREM Spec => Stabilization
=============================================================================