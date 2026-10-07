----------------------------- MODULE DijkstraTokenRing -----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS N, M

(*
  Assumptions:
  - At least one node and a nonempty value domain.
  - Domain of counter values is 0..M-1.
  - Classical Dijkstra constraint: N <= M + 1.
*)
ASSUME N \in Nat /\ N >= 1
ASSUME M \in Nat /\ M >= 1
ASSUME N <= M + 1

(*
  Nodes are arranged in a ring: 0..N-1
  Each node i stores a counter v[i] in 0..M-1
*)
VARIABLES v

Nodes == 0..(N - 1)
Vals  == 0..(M - 1)

Pred(i) == IF i = 0 THEN N - 1 ELSE i - 1

Inc(x) == IF x = M - 1 THEN 0 ELSE x + 1

(*
  Type correctness invariant: each node's value is in the bounded domain.
*)
TypeOK == v \in [Nodes -> Vals]

(*
  Initialization: arbitrary configuration (self-stabilization from any state).
*)
Init == TypeOK

(*
  Algorithm steps (interleaving semantics; one process acts at a time):
  - Node 0:
      If v[0] = v[N-1], it creates a new token by incrementing its value mod M.
      Otherwise, it copies its predecessor's value.
  - Node i > 0:
      If v[i] # v[i-1], it copies its predecessor's value (passes the token).
*)
Node0Step ==
  LET p == N - 1 IN
    v' = [v EXCEPT
            ![0] = IF v[0] = v[p] THEN Inc(@) ELSE v[p]
         ]

NodeIStep(i) ==
  i \in 1..(N - 1)
  /\ v[i] # v[Pred(i)]
  /\ v' = [v EXCEPT ![i] = v[Pred(i)]]

Step(i) == IF i = 0 THEN Node0Step ELSE NodeIStep(i)

Next == \E i \in Nodes: Step(i)

(*
  Token/privilege definition (classical for Dijkstra's ring):
  - For i > 0: token present at i iff v[i] # v[i-1].
  - For i = 0: token present at 0 iff v[0] = v[N-1].
*)
TokenAt(i) ==
  IF i = 0 THEN v[0] = v[N - 1] ELSE v[i] # v[Pred(i)]

TokenSet == { i \in Nodes: TokenAt(i) }
UniqueToken == Cardinality(TokenSet) = 1

(*
  Liveness (stabilization): eventually the system reaches and stays
  in a state with a unique token.
*)
Stabilization == <>[] UniqueToken

(*
  Full behavior specification with weak fairness for each process action.
*)
Spec == Init
        /\ [][Next]_v
        /\ \A i \in Nodes: WF_v(Step(i))

=============================