---------------------------- MODULE TokenRing ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, K

ASSUME NPositive == N > 0
ASSUME KGreaterThanN == K > N

VARIABLES counter

vars == <<counter>>

Proc == 0..(N-1)
Counter == 0..(K-1)

TypeOK == counter \in [Proc -> Counter]

Predecessor(i) == IF i = 0 THEN N - 1 ELSE i - 1

HasToken(i) ==
    IF i = 0
    THEN counter[0] = counter[N-1]
    ELSE counter[i] # counter[Predecessor(i)]

TokenHolders == {i \in Proc : HasToken(i)}

Init == counter \in [Proc -> Counter]

Process0Step ==
    /\ HasToken(0)
    /\ counter' = [counter EXCEPT ![0] = (counter[0] + 1) % K]

ProcessIStep(i) ==
    /\ i \in 1..(N-1)
    /\ HasToken(i)
    /\ counter' = [counter EXCEPT ![i] = counter[Predecessor(i)]]

Next ==
    \/ Process0Step
    \/ \E i \in 1..(N-1) : ProcessIStep(i)

Fairness ==
    /\ WF_vars(Process0Step)
    /\ \A i \in 1..(N-1) : WF_vars(ProcessIStep(i))

Spec == Init /\ [][Next]_vars /\ Fairness

TokenExists == TokenHolders # {}

SingleToken == Cardinality(TokenHolders) = 1

TokenExistsInvariant == TokenExists

EventuallyAlwaysSingleToken == <>[]SingleToken

Process0EventuallyMoves == []<><<Process0Step>>_vars

TokenCirculates == \A i \in Proc : []<>(HasToken(i))

Liveness ==
    /\ EventuallyAlwaysSingleToken
    /\ Process0EventuallyMoves

==========================================================================