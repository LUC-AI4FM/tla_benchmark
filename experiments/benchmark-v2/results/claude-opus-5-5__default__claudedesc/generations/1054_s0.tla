------------------------------ MODULE TokenRing ------------------------------
(***************************************************************************)
(* Dijkstra's self-stabilizing token ring algorithm (EWD426).             *)
(* N nodes, numbered 0..N-1, each holding a counter c[i] in 0..M-1.       *)
(* Tokens are not explicit. They are defined by the relationships         *)
(* between neighboring counters.                                          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, M

ASSUME NMAssumption == /\ N \in Nat \ {0}
                       /\ M \in Nat \ {0}
                       /\ N <= M + 1

Node == 0 .. N-1

VARIABLES c

vars == << c >>

TypeOK == c \in [Node -> 0 .. M-1]

(***************************************************************************)
(* There is exactly one token in the ring. The counters c[0]..c[i] all    *)
(* equal c[0], and the counters c[i+1]..c[N-1] all equal (c[0]-1) % M.    *)
(* If i < N-1, the token is at node i+1. If i = N-1, all counters are     *)
(* equal and the token is at node 0.                                      *)
(***************************************************************************)
UniqueToken(i) ==
    /\ \A j \in 0 .. i : c[j] = c[0]
    /\ \A j \in (i+1) .. (N-1) : c[j] = (c[0] - 1) % M

-----------------------------------------------------------------------------

Init == c \in [Node -> 0 .. M-1]

CreateToken ==
    /\ c[0] = c[N-1]
    /\ c' = [c EXCEPT ![0] = (c[0] + 1) % M]

PassToken(i) ==
    /\ i # 0
    /\ c[i] # c[i-1]
    /\ c' = [c EXCEPT ![i] = c[i-1]]

Next ==
    \/ CreateToken
    \/ \E i \in Node \ {0} : PassToken(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------

Stab == <>[] \E i \in Node : UniqueToken(i)

THEOREM Spec => []TypeOK
THEOREM Spec => Stab

=============================================================================