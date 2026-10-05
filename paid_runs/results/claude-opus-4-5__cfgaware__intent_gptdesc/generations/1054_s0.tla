---------------------------- MODULE TokenRing ----------------------------

EXTENDS Naturals, Integers

CONSTANTS N, M

ASSUME N \in Nat /\ N >= 2
ASSUME M \in Nat /\ M >= N + 1

VARIABLES counter

vars == <<counter>>

Procs == 0..(N-1)

Domain == 0..(M-1)

TypeInvariant == counter \in [Procs -> Domain]

Pred(i) == IF i = 0 THEN N - 1 ELSE i - 1

SourceEnabled == TRUE

SourceAction ==
    /\ counter' = [counter EXCEPT ![0] = (counter[0] + 1) % M]

NonSourceEnabled(i) ==
    /\ i \in 1..(N-1)
    /\ counter[i] # counter[Pred(i)]

NonSourceAction(i) ==
    /\ NonSourceEnabled(i)
    /\ counter' = [counter EXCEPT ![i] = counter[Pred(i)]]

Init ==
    counter \in [Procs -> Domain]

Next ==
    \/ SourceAction
    \/ \E i \in 1..(N-1) : NonSourceAction(i)

CountBoundaries ==
    LET boundary(i) == IF counter[i] # counter[Pred(i)] THEN 1 ELSE 0
    IN LET sum[i \in 0..N] ==
           IF i = 0 THEN 0
           ELSE sum[i-1] + boundary(i-1)
       IN sum[N]

UniqueTokenConfig ==
    CountBoundaries = 1

ValidBoundary ==
    \A i \in Procs :
        counter[i] # counter[Pred(i)] =>
            \/ counter[i] = (counter[Pred(i)] + 1) % M
            \/ counter[Pred(i)] = (counter[i] + 1) % M

StableConfig ==
    /\ UniqueTokenConfig
    /\ \E i \in Procs :
        /\ counter[i] # counter[Pred(i)]
        /\ counter[i] = (counter[Pred(i)] + 1) % M

Safety == TypeInvariant

Stabilization == <>[]StableConfig

Fairness ==
    /\ WF_vars(SourceAction)
    /\ \A i \in 1..(N-1) : WF_vars(NonSourceAction(i))

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

Liveness == Stabilization

==========================================================================