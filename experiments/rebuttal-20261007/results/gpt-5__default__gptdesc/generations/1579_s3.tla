------------------------------- MODULE DijkstraTokenRing -------------------------------

EXTENDS Naturals, Integers

CONSTANTS N, K

ASSUME N \in Nat /\ N > 0 /\ K \in Nat /\ K > N

VARIABLES x

Proc == 0..(N-1)
Val  == 0..(K-1)

TypeOK == x \in [Proc -> Val]

Pred(i) == IF i = 0 THEN N-1 ELSE i-1

Token(i) ==
  IF i = 0
    THEN x[0] = x[N-1]
    ELSE x[i] # x[Pred(i)]

SomeToken == \E i \in Proc: Token(i)

OneToken ==
  \E i \in Proc:
    Token(i) /\ \A j \in Proc: Token(j) => j = i

Init == TypeOK

Step(i) ==
  IF i = 0
    THEN /\ x[i] = x[Pred(i)]
         /\ x' = [x EXCEPT ![i] = (x[i] + 1) % K]
    ELSE /\ x[i] # x[Pred(i)]
         /\ x' = [x EXCEPT ![i] = x[Pred(i)]]

Next == \E i \in Proc: Step(i)

Fairness == \A i \in Proc: WF_x(Step(i))

Spec == Init /\ [][Next]_x /\ Fairness

THEOREM TypeInvariant == Spec => []TypeOK
PROOF OMITTED

THEOREM AlwaysSomeToken == Spec => []SomeToken
PROOF OMITTED

THEOREM Convergence == Spec => <>[] OneToken
PROOF OMITTED

=============================================================================