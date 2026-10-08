---------------------------- MODULE TokenRing ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS N, K

ASSUME N > 0
ASSUME K > N

VARIABLES counter

vars == <<counter>>

Procs == 0..(N-1)

States == 0..(K-1)

Predecessor(i) == IF i = 0 THEN N - 1 ELSE i - 1

HasToken(i) ==
    IF i = 0 
    THEN counter[0] = counter[N - 1]
    ELSE counter[i] # counter[Predecessor(i)]

TokenHolders == {i \in Procs : HasToken(i)}

SomeoneHoldsToken == TokenHolders # {}

ExactlyOneHoldsToken == Cardinality(TokenHolders) = 1

TypeOK == counter \in [Procs -> States]

Init == counter \in [Procs -> States]

Process0Step ==
    /\ HasToken(0)
    /\ counter' = [counter EXCEPT ![0] = (counter[0] + 1) % K]

ProcessIStep(i) ==
    /\ i > 0
    /\ HasToken(i)
    /\ counter' = [counter EXCEPT ![i] = counter[Predecessor(i)]]

Next ==
    \/ Process0Step
    \/ \E i \in 1..(N-1) : ProcessIStep(i)

Fairness ==
    /\ WF_vars(Process0Step)
    /\ \A i \in 1..(N-1) : WF_vars(ProcessIStep(i))

Spec == Init /\ [][Next]_vars /\ Fairness

EventuallyJustOneHoldsToken == <>[]ExactlyOneHoldsToken

TokenCirculates == []<><<Next>>_vars

==========================================================================