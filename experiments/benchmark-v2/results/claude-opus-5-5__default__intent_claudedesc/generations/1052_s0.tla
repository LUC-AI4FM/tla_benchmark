---------------------------- MODULE TokenRing ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, M

ASSUME NAssumption == N \in Nat /\ N >= 1
ASSUME MAssumption == M \in Nat /\ M >= 2

VARIABLES x

vars == << x >>

Procs == 0 .. (N - 1)

Values == 0 .. (M - 1)

Pred(i) == IF i = 0 THEN N - 1 ELSE i - 1

HasToken(i) ==
    IF i = 0
        THEN x[0] = x[N - 1]
        ELSE x[i] # x[i - 1]

TokenHolders == { i \in Procs : HasToken(i) }

TypeOK == x \in [Procs -> Values]

Init == x = [i \in Procs |-> 0]

Move(i) ==
    /\ HasToken(i)
    /\ IF i = 0
          THEN x' = [x EXCEPT ![0] = (x[0] + 1) % M]
          ELSE x' = [x EXCEPT ![i] = x[i - 1]]

Next == \E i \in Procs : Move(i)

Fairness == \A i \in Procs : WF_vars(Move(i))

Spec == Init /\ [][Next]_vars /\ Fairness

MutualExclusion ==
    \A i, j \in Procs : (HasToken(i) /\ HasToken(j)) => i = j

ExactlyOneToken == Cardinality(TokenHolders) = 1

DeadlockFreedom == \E i \in Procs : HasToken(i)

Progress == ENABLED Next

TokenCirculation == \A i \in Procs : []<>HasToken(i)

NoStarvation == \A i \in Procs : <>HasToken(i)

TokenEventuallyPasses ==
    \A i \in Procs : HasToken(i) ~> HasToken((i + 1) % N)

AlwaysProgress == []Progress

THEOREM Spec => [](TypeOK /\ MutualExclusion /\ ExactlyOneToken /\ DeadlockFreedom)
THEOREM Spec => TokenCirculation /\ TokenEventuallyPasses
=============================================================================