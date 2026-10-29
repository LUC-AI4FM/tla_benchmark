---------------------------- MODULE BoundedCounters ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

ASSUME NAssumption      == N \in Nat /\ N >= 1
ASSUME MaxNatAssumption == MaxNat \in Nat /\ MaxNat >= 1

\* Finite stand-in for Nat, used for model checking (Nat <- NatOverride)
NatOverride == 0..(N + MaxNat)

Procs == 1..N

Values == 0..(MaxNat - 1)

VARIABLES counter, lastRead

vars == <<counter, lastRead>>

-----------------------------------------------------------------------------

TypeOK ==
    /\ counter \in [Procs -> Values]
    /\ lastRead \in [Procs -> [Procs -> Values]]

Init ==
    /\ counter \in [Procs -> Values]
    /\ lastRead = [p \in Procs |-> [q \in Procs |-> 0]]

\* An increment is enabled only if it keeps the counter strictly below MaxNat
Inc(p) ==
    /\ counter[p] + 1 < MaxNat
    /\ counter' = [counter EXCEPT ![p] = counter[p] + 1]
    /\ UNCHANGED lastRead

\* A decrement is enabled only if it keeps the counter nonnegative
Dec(p) ==
    /\ counter[p] > 0
    /\ counter' = [counter EXCEPT ![p] = counter[p] - 1]
    /\ UNCHANGED lastRead

\* Process p reads process q's counter
Read(p, q) ==
    /\ p # q
    /\ lastRead' = [lastRead EXCEPT ![p][q] = counter[q]]
    /\ UNCHANGED counter

Next ==
    \/ \E p \in Procs : Inc(p)
    \/ \E p \in Procs : Dec(p)
    \/ \E p, q \in Procs : Read(p, q)

Fairness ==
    /\ \A p \in Procs : WF_vars(Inc(p))
    /\ \A p \in Procs : WF_vars(Dec(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

NonNegative == \A p \in Procs : counter[p] >= 0

BelowMax == \A p \in Procs : counter[p] < MaxNat

IntegerCounters == \A p \in Procs : counter[p] \in 0..MaxNat

\* Every locally held value (own counter or a read copy) respects the global bound
MutualExclusion ==
    /\ \A p \in Procs : counter[p] \in Values
    /\ \A p, q \in Procs : lastRead[p][q] \in Values

BoundIsFixedNat == MaxNat \in Nat /\ MaxNat >= 1

Inv ==
    /\ TypeOK
    /\ NonNegative
    /\ BelowMax
    /\ IntegerCounters
    /\ MutualExclusion
    /\ BoundIsFixedNat

\* Each process modifies only its own counter
OnlyOwnCounter ==
    [][\A p \in Procs :
         counter'[p] # counter[p] =>
            \A q \in Procs \ {p} : counter'[q] = counter[q]]_vars

-----------------------------------------------------------------------------
\* Liveness properties

IncProgress ==
    \A p \in Procs :
        []<>(~ENABLED <<Inc(p)>>_vars) \/ []<><<Inc(p)>>_vars

DecProgress ==
    \A p \in Procs :
        []<>(~ENABLED <<Dec(p)>>_vars) \/ []<><<Dec(p)>>_vars

Liveness == IncProgress /\ DecProgress

-----------------------------------------------------------------------------

StateConstraint == \A p \in Procs : counter[p] < MaxNat

THEOREM Spec => []Inv
THEOREM Spec => Liveness
=============================================================================