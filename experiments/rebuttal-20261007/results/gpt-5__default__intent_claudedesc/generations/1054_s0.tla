------------------------------ MODULE EWD426TokenRing ------------------------------

EXTENDS Naturals

CONSTANTS N, M

ASSUME
  /\ N \in Nat /\ N >= 1
  /\ M \in Nat /\ M >= 1
  /\ N <= M + 1

VARIABLES x

Indices == 0..(N - 1)
Values  == 0..(M - 1)

Pred(i) == IF i = 0 THEN N - 1 ELSE i - 1

NextVal(v) == IF v < M - 1 THEN v + 1 ELSE 0

TypeOK == x \in [Indices -> Values]

\* Token predicate: node 0 has a token when x[0] = x[N-1];
\* any other node i>0 has a token when x[i] # x[i-1].
TokenAt(i) ==
  /\ i \in Indices
  /\ IF i = 0 THEN x[i] = x[Pred(i)] ELSE x[i] # x[Pred(i)]

AtLeastOneToken == \E i \in Indices: TokenAt(i)

UniqueToken ==
  \E i \in Indices:
    /\ TokenAt(i)
    /\ \A j \in Indices: TokenAt(j) => j = i

\* Descriptive “two-block” shape from node 0 to the unique transition.
PreBlock(k)  == \A j \in 0..k: x[j] = x[0]
PostBlock(k) == \A j \in (k + 1)..(N - 1): x[j] = x[k]
BlockShape(k) == /\ k \in Indices /\ PreBlock(k) /\ PostBlock(k)
BlockUnique ==
  \E k \in Indices:
    /\ BlockShape(k)
    /\ \A j \in Indices: BlockShape(j) => j = k

Init == TypeOK

NodeStep(i) ==
  /\ i \in Indices
  /\ IF i = 0 THEN x[i] = x[Pred(i)] ELSE x[i] # x[Pred(i)]
  /\ x' = [x EXCEPT ![i] =
             IF i = 0 THEN NextVal(@) ELSE x[Pred(i)]]

Next == \E i \in Indices: NodeStep(i)

Fairness == \A i \in Indices: WF_x(NodeStep(i))

Spec == /\ Init
        /\ [][Next]_x
        /\ Fairness

\* Safety invariants (state properties that should hold in all states)
SafetyInv == /\ TypeOK
             /\ AtLeastOneToken

AlwaysSafety == []SafetyInv

\* Liveness (stabilization): eventually, from some point on,
\* there is exactly one token (and thus the two-block shape holds).
Stabilization == <>[]UniqueToken

=============================================================================