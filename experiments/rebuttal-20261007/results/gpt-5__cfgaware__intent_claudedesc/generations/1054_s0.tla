---- MODULE EWD426 ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, M

(*
  Ring size N, counter domain size M, with the requirement N <= M + 1.
  Both N and M are positive naturals.
*)
ASSUME N \in Nat /\ N > 0 /\ M \in Nat /\ M > 0 /\ N <= M + 1

VARIABLES c

vars == << c >>

Node == 0..(N - 1)

Pred(i) == (i - 1) % N

IncM(x) == (x + 1) % M

TypeOK == c \in [Node -> 0..(M - 1)]

Init == TypeOK

(*
  Token predicate per EWD426:
  - Node 0 is privileged (has the token) iff c[0] = c[Pred(0)].
  - Any other node i > 0 is privileged iff c[i] # c[Pred(i)].
*)
Token(i) == IF i = 0 THEN c[0] = c[Pred(0)] ELSE c[i] # c[Pred(i)]

Tokens == { i \in Node : Token(i) }

OneToken == Cardinality(Tokens) = 1
Stable == OneToken

(*
  Actions:
  - Node 0 (when privileged) increments its counter modulo M.
  - Node i > 0 (when privileged) copies its predecessor's counter.
*)
Act(i) ==
  /\ i \in Node
  /\ IF i = 0
        THEN /\ c[0] = c[Pred(0)]
             /\ c' = [c EXCEPT ![0] = IncM(@)]
        ELSE /\ c[i] # c[Pred(i)]
             /\ c' = [c EXCEPT ![i] = c[Pred(i)]]

Next == \E i \in Node : Act(i)

(*
  System specification: arbitrary initial configuration; standard stuttering;
  weak fairness on every node action.
*)
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in Node : WF_vars(Act(i))

(*
  Liveness (stabilization): eventually, from some point on, there is exactly one token forever.
*)
Stabilizes == <>[]Stable

====