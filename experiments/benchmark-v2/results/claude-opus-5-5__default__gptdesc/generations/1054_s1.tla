------------------------------- MODULE EWD426 -------------------------------
(***************************************************************************)
(* Dijkstra's self-stabilizing token ring algorithm (EWD426), K-state     *)
(* version. N nodes 0..N-1 form a ring, and each holds a counter in       *)
(* 0..M-1.                                                                *)
(*                                                                         *)
(* - Node 0 holds a token when its value equals the last node's value.    *)
(*   It passes the token by setting its value to (c[N-1] + 1) % M.        *)
(* - Node i > 0 holds a token when its value differs from its             *)
(*   predecessor's value. It passes the token by copying c[i-1].          *)
(*                                                                         *)
(* When N <= M + 1, the system eventually reaches a state with exactly    *)
(* one token and stays in such states forever after.                      *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, M

ASSUME NAssumption  == N \in Nat \ {0}
ASSUME MAssumption  == M \in Nat \ {0}
ASSUME NMAssumption == N <= M + 1

Node   == 0 .. N-1
Values == 0 .. M-1

VARIABLE c

vars == << c >>

TypeOK == c \in [Node -> Values]

(* Predicate: node i currently holds a token (is privileged). *)
HasToken(i) ==
    IF i = 0 THEN c[0] = c[N-1]
             ELSE c[i] # c[i-1]

TokenHolders == { i \in Node : HasToken(i) }

(* Any initial configuration is allowed (self-stabilization). *)
Init == c \in [Node -> Values]

(* Node 0 creates a new token. *)
CreateToken ==
    /\ HasToken(0)
    /\ c' = [c EXCEPT ![0] = (c[N-1] + 1) % M]

(* Node i > 0 passes the token by copying its predecessor. *)
PassToken(i) ==
    /\ i # 0
    /\ HasToken(i)
    /\ c' = [c EXCEPT ![i] = c[i-1]]

Next == CreateToken \/ \E i \in Node \ {0} : PassToken(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety: types are preserved, and at least one token always exists,     *)
(* so the system never deadlocks.                                         *)
AtLeastOneToken == TokenHolders # {}

(* Legitimate states have exactly one token. *)
UniqueToken == Cardinality(TokenHolders) = 1

(* Stabilization: eventually the system has a unique token forever. *)
Stabilization == <>[]UniqueToken

(* Closure: once a unique token exists, it remains unique. *)
Closure == [](UniqueToken => []UniqueToken)

THEOREM Spec => []TypeOK /\ []AtLeastOneToken
THEOREM Spec => Stabilization
=============================================================================