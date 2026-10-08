---- MODULE DijkstraTokenRing ----
EXTENDS Naturals, TLC

CONSTANTS N, K

ASSUME /\ N \in Nat /\ K \in Nat
       /\ N > 0
       /\ K > N

VARIABLES M, pc

ProcSet == 0..(N - 1)

Init ==
  /\ M \in [ProcSet -> 0..(K - 1)]
  /\ pc = [i \in ProcSet |-> "try"]

Token(i, m) ==
  IF i = 0 THEN m[0] = m[N - 1] ELSE m[i] # m[i - 1]

Holders(m) == { i \in ProcSet : Token(i, m) }

Try(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "try"
  /\ Token(i, M)
  /\ pc' = [pc EXCEPT ![i] = "do"]
  /\ UNCHANGED M

Do(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "do"
  /\ M' = IF i = 0
            THEN [M EXCEPT ![0] = (M[0] + 1) % K]
            ELSE [M EXCEPT ![i] = M[i - 1]]
  /\ pc' = [pc EXCEPT ![i] = "try"]

Next ==
  \E i \in ProcSet : Try(i) \/ Do(i)

vars == << M, pc >>

Spec ==
  Init /\ [][Next]_vars /\ \A i \in ProcSet : WF_vars(Try(i) \/ Do(i))

SomeoneHoldsToken ==
  Holders(M) # {}

EventuallyJustOneHoldsToken ==
  <>[] (Cardinality(Holders(M)) = 1)
====