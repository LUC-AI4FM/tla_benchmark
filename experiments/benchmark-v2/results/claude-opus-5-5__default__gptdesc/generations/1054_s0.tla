---------------------------- MODULE EWD426 ----------------------------
(***************************************************************************)
(* Dijkstra's self-stabilizing token ring (EWD426), K-state version.       *)
(* N nodes, numbered 0..N-1, are arranged in a ring. Each node holds a     *)
(* counter in 0..M-1. Node 0 is the distinguished "bottom" node. It holds  *)
(* a privilege (token) when its value equals that of node N-1. It then     *)
(* creates a new token by setting its value to (c[N-1] + 1) % M. Every     *)
(* other node i holds a privilege when its value differs from its          *)
(* predecessor's. It passes the token by copying c[i-1].                   *)
(* The system starts in an arbitrary state. Stabilization means it         *)
(* eventually reaches and stays in a state with exactly one token.         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, M

ASSUME NAssump  == N \in Nat \ {0}
ASSUME MAssump  == M \in Nat \ {0}
ASSUME NMAssump == N <= M + 1

Node == 0 .. N-1
Val  == 0 .. M-1

VARIABLE c

vars == << c >>

TypeOK == c \in [Node -> Val]

(* Node i holds a token in the current state *)
HasToken(i) ==
  IF i = 0 THEN c[0] = c[N-1]
           ELSE c[i] # c[i-1]

TokenSet == { i \in Node : HasToken(i) }

(* Arbitrary initial state: self-stabilization *)
Init == c \in [Node -> Val]

(* Bottom node creates a new token *)
CreateToken ==
  /\ HasToken(0)
  /\ c' = [c EXCEPT ![0] = (c[N-1] + 1) % M]

(* Node i > 0 passes the token by copying its predecessor *)
PassToken(i) ==
  /\ i # 0
  /\ HasToken(i)
  /\ c' = [c EXCEPT ![i] = c[i-1]]

Next ==
  \/ CreateToken
  \/ \E i \in Node \ {0} : PassToken(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety: type correctness. There is also always at least one token. *)
TypeInvariant == TypeOK

AlwaysSomeToken == TokenSet # {}

UniqueToken == Cardinality(TokenSet) = 1

(* Liveness: the system eventually stabilizes to a unique token forever *)
Stabilization == <>[]UniqueToken

THEOREM Spec => [](TypeInvariant /\ AlwaysSomeToken)
THEOREM Spec => Stabilization
=============================================================================