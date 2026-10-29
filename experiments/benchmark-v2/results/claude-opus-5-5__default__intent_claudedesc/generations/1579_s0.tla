---------------------------- MODULE TokenRing ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, K

ASSUME NK == /\ N \in Nat \ {0}
             /\ K \in Nat
             /\ K > N

VARIABLE c

vars == << c >>

Procs == 0 .. (N - 1)
Vals  == 0 .. (K - 1)

TypeOK == c \in [Procs -> Vals]

HasToken(i) == IF i = 0 THEN c[0] = c[N - 1]
                        ELSE c[i] # c[i - 1]

TokenHolders == { i \in Procs : HasToken(i) }

(* Dijkstra's algorithm is self-stabilizing: any initial configuration *)
Init == c \in [Procs -> Vals]

Move(i) == /\ HasToken(i)
           /\ c' = [c EXCEPT ![i] = IF i = 0 THEN (c[0] + 1) % K
                                             ELSE c[i - 1]]

Next == \E i \in Procs : Move(i)

Fairness == \A i \in Procs : WF_vars(Move(i))

Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
(* Safety: at least one process always holds the token *)
AtLeastOneToken == \E i \in Procs : HasToken(i)

UniqueToken == Cardinality(TokenHolders) = 1

(* Liveness: eventually exactly one process holds the token, forever *)
Stabilization == <>[]UniqueToken

THEOREM Spec => []TypeOK
THEOREM Spec => []AtLeastOneToken
THEOREM Spec => Stabilization
============================================================================