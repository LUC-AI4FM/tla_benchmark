---------------------------- MODULE TokenRing ----------------------------
(***************************************************************************)
(* Dijkstra's self-stabilizing token ring algorithm (EWD426).              *)
(* N nodes in a ring, numbered 0..N-1, each holding a counter in 0..M-1.   *)
(* Node 0 holds a token when its value equals that of node N-1, and it     *)
(* passes the token on by incrementing its value modulo M relative to      *)
(* node N-1. Any other node i holds a token when its value differs from    *)
(* that of node i-1, and it passes the token on by copying node i-1's      *)
(* value. Starting from an arbitrary state, the system eventually reaches  *)
(* and remains in states with exactly one token.                           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, M

ASSUME NAssump  == N \in Nat /\ N >= 1
ASSUME MAssump  == M \in Nat /\ M >= 1
ASSUME NMAssump == N <= M + 1

Node  == 0 .. N-1
Value == 0 .. M-1

VARIABLE c

vars == << c >>

TypeOK == c \in [Node -> Value]

-----------------------------------------------------------------------------
(* Token predicates *)

HasToken(i) ==
    IF i = 0 THEN c[0] = c[N-1]
             ELSE c[i] # c[i-1]

-----------------------------------------------------------------------------
(* Initial state: arbitrary (self-stabilization) *)

Init == c \in [Node -> Value]

(* Node 0 creates a new token *)
CreateToken ==
    /\ c[0] = c[N-1]
    /\ c' = [c EXCEPT ![0] = (c[N-1] + 1) % M]

(* Node i > 0 passes the token by copying its predecessor *)
PassToken(i) ==
    /\ i # 0
    /\ c[i] # c[i-1]
    /\ c' = [c EXCEPT ![i] = c[i-1]]

Next == CreateToken \/ \E i \in Node \ {0} : PassToken(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Properties *)

TokenHolders == { i \in Node : HasToken(i) }

(* There is always at least one token, so the system never deadlocks *)
AtLeastOneToken == TokenHolders # {}

UniqueToken == Cardinality(TokenHolders) = 1

(* Stabilization: eventually the system reaches and stays in a state *)
(* with a unique token.                                               *)
Stabilization == <>[]UniqueToken

THEOREM Spec => []TypeOK
THEOREM Spec => []AtLeastOneToken
THEOREM Spec => Stabilization
=============================================================================