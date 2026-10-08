---------------------------- MODULE StabilizingTokenRing ----------------------------
EXTENDS Integers, Naturals, FiniteSets

CONSTANTS N, M

ASSUME NPositive == N > 0
ASSUME MPositive == M > 0
ASSUME StabilizationPossible == M >= N

VARIABLES counter

vars == <<counter>>

Proc == 0..(N-1)

Domain == 0..(M-1)

Pred(i) == IF i = 0 THEN N - 1 ELSE i - 1

TypeInvariant == counter \in [Proc -> Domain]

SourceInject ==
    /\ counter' = [counter EXCEPT ![0] = (counter[0] + 1) % M]

PassToken(i) ==
    /\ i \in 1..(N-1)
    /\ counter[i] # counter[Pred(i)]
    /\ counter' = [counter EXCEPT ![i] = counter[Pred(i)]]

SourceEnabled == TRUE

PassEnabled(i) == counter[i] # counter[Pred(i)]

Init == counter \in [Proc -> Domain]

Next ==
    \/ SourceInject
    \/ \E i \in 1..(N-1) : PassToken(i)

CountBoundaries ==
    Cardinality({i \in Proc : counter[i] # counter[Pred(i)]})

UniqueTokenConfig ==
    CountBoundaries = 1

ConsecutiveValues ==
    \A i \in Proc :
        counter[i] = counter[Pred(i)] 
        \/ counter[i] = (counter[Pred(i)] + 1) % M

CanonicalConfig ==
    /\ UniqueTokenConfig
    /\ ConsecutiveValues

TokenLocation ==
    IF UniqueTokenConfig
    THEN CHOOSE i \in Proc : counter[i] # counter[Pred(i)]
    ELSE -1

SafetyInvariant == TypeInvariant

EventualStabilization == <>[]CanonicalConfig

TokenCirculates ==
    []<>(SourceInject)

Fairness ==
    /\ WF_vars(SourceInject)
    /\ \A i \in 1..(N-1) : WF_vars(PassToken(i))

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

LivenessProperty == EventualStabilization

THEOREM Spec => []SafetyInvariant

THEOREM Spec => LivenessProperty

=============================================================================