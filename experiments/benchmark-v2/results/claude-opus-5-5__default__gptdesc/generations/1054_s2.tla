---------------------------- MODULE EWD426 ----------------------------
(***************************************************************************)
(* Dijkstra's self-stabilizing token ring (EWD426), K-state version.       *)
(* N nodes are arranged in a ring and numbered 0..N-1. Each node holds a   *)
(* counter in 0..M-1.                                                      *)
(*   - Node 0 holds a token iff its value equals the value of node N-1.    *)
(*     It creates a new token by incrementing (mod M) relative to the      *)
(*     value of node N-1.                                                  *)
(*   - Node i > 0 holds a token iff its value differs from that of node    *)
(*     i-1. It passes the token by copying its predecessor's value.        *)
(* The system starts in an arbitrary state. It eventually reaches a state  *)
(* with exactly one token and stays in such states.                        *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, M

ASSUME NAssumption  == N \in Nat \ {0}
ASSUME MAssumption  == M \in Nat \ {0}
ASSUME RingBound    == N <= M + 1

VARIABLE c

vars == << c >>

Nodes  == 0 .. N-1
Values == 0 .. M-1

TypeOK == c \in [Nodes -> Values]

(* Token predicate for each node *)
HasToken(i) ==
    IF i = 0 THEN c[0] = c[N-1]
             ELSE c[i] # c[i-1]

TokenHolders == { i \in Nodes : HasToken(i) }

(* Any state is a valid initial state: self-stabilization *)
Init == c \in [Nodes -> Values]

(* Node 0 creates a new token *)
CreateToken ==
    /\ HasToken(0)
    /\ c' = [c EXCEPT ![0] = (c[N-1] + 1) % M]

(* Node i > 0 passes the token by copying its predecessor *)
PassToken(i) ==
    /\ i # 0
    /\ HasToken(i)
    /\ c' = [c EXCEPT ![i] = c[i-1]]

Next == CreateToken \/ \E i \in Nodes \ {0} : PassToken(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety: type correctness *)
TypeInvariant == TypeOK

(* There is always at least one token (no deadlock) *)
AtLeastOneToken == TokenHolders # {}

(* Exactly one token present *)
UniqueToken == Cardinality(TokenHolders) = 1

(* Stabilization: eventually the system reaches and remains in a state *)
(* with a unique token.                                                *)
Stabilization == <>[]UniqueToken

THEOREM Spec => []TypeInvariant
THEOREM Spec => []AtLeastOneToken
THEOREM Spec => Stabilization
=============================================================================