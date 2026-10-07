----------------------------- MODULE DijkstraTokenRing -----------------------------

EXTENDS Naturals, Integers

CONSTANTS N, K

ASSUME /\ N \in Nat \ {0}
       /\ K \in Nat
       /\ K > N

VARIABLES x

ProcSet == 0..(N - 1)
ValSet  == 0..(K - 1)

Pred(i) == IF i = 0 THEN N - 1 ELSE i - 1

Init == x \in [ProcSet -> ValSet]

Token(i) ==
  IF i = 0
    THEN x[i] = x[Pred(i)]
    ELSE x[i] # x[Pred(i)]

SomeToken == \E i \in ProcSet : Token(i)
OneToken  == \E! i \in ProcSet : Token(i)

Step(i) ==
  /\ i \in ProcSet
  /\ IF i = 0
        THEN /\ x[i] = x[Pred(i)]
             /\ x' = [x EXCEPT ![i] = (x[i] + 1) % K]
        ELSE /\ x[i] # x[Pred(i)]
             /\ x' = [x EXCEPT ![i] = x[Pred(i)]]

Next == \E i \in ProcSet : Step(i)

Spec == Init /\ [][Next]_x /\ \A i \in ProcSet : WF_x(Step(i))

TypeInv == x \in [ProcSet -> ValSet]

Safety == [] SomeToken
Convergence == <> OneToken

THEOREM Spec => []TypeInv
THEOREM Spec => Safety
THEOREM Spec => Convergence

=============================================================================