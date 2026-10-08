MODULE TokenRing
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, M, SOURCE

ASSUME
    N >= 2
    /\ M > 1
    /\ 1 <= SOURCE <= N

VARIABLE counters

DOMAIN == {0 .. M-1}

Predecessor(i) ==
    IF i = 1 THEN N ELSE i - 1

Init ==
    counters \in [1..N -> DOMAIN]

SourceInject ==
    LET newVal == Mod(counters[SOURCE] + 1, M) IN
        counters' = [counters EXCEPT ![SOURCE] = newVal]
        /\ UNCHANGED <<>>

CopyAction(i) ==
    i \in 1..N /\
    counters' = [counters EXCEPT ![i] = counters[Predecessor(i)]]
    /\ UNCHANGED <<>>

Next == SourceInject \/ \E i \in 1..N : CopyAction(i)

ChangeIndices(c) ==
    {i \in 1..N : c[i] # c[Predecessor(i)]}

UniqueToken(c) ==
    LET changes == ChangeIndices(c)
    IN
        /\ Cardinality(changes) = 1
        /\ \A i \in changes :
            c[i] = Mod(c[Predecessor(i)] - 1, M)

Safe ==
    \A i \in 1..N : counters[i] \in DOMAIN

Stabilization ==
    <> UniqueToken(counters)
    /\ [] (UniqueToken(counters) => [] UniqueToken(counters))

Spec == Init
        /\ [][Next]_counters
        /\ WF_vars(SourceInject)
        /\ WF_vars(\E i \in 1..N : CopyAction(i))
        /\ Safe

THEOREM Safety: Spec => []Safe

THEOREM StabilizationTheorem: Spec => Stabilization