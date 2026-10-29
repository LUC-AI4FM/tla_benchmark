------------------------------ MODULE BoundedDistributedCounter ------------------------------
EXTENDS Naturals, Integers, FiniteSets

CONSTANTS
    Proc,       \* the finite set of processes
    Max         \* fixed strict upper bound on every counter

ASSUME MaxIsNat     == Max \in Nat /\ Max > 0
ASSUME ProcNonEmpty == Proc # {} /\ IsFiniteSet(Proc)

VARIABLES
    count,      \* count[p] : the local counter owned by process p
    lastRead    \* lastRead[p][q] : the value of q's counter most recently read by p

vars == <<count, lastRead>>

CounterRange == 0..(Max - 1)

-----------------------------------------------------------------------------
(* Type invariant                                                           *)
-----------------------------------------------------------------------------
TypeOK ==
    /\ count \in [Proc -> CounterRange]
    /\ lastRead \in [Proc -> [Proc -> CounterRange]]

-----------------------------------------------------------------------------
(* Initial condition: every counter is nonnegative and strictly below Max *)
-----------------------------------------------------------------------------
Init ==
    /\ count \in [Proc -> CounterRange]
    /\ lastRead = [p \in Proc |-> count]

-----------------------------------------------------------------------------
(* Actions                                                                  *)
-----------------------------------------------------------------------------

\* Attempted increment. It is disabled if the result would reach or exceed Max.
Inc(p) ==
    /\ count[p] + 1 < Max
    /\ count' = [count EXCEPT ![p] = count[p] + 1]
    /\ UNCHANGED lastRead

\* Attempted decrement. It is disabled if the result would be negative.
Dec(p) ==
    /\ count[p] - 1 >= 0
    /\ count' = [count EXCEPT ![p] = count[p] - 1]
    /\ UNCHANGED lastRead

\* Process p reads the counter of another process q.
Read(p, q) ==
    /\ q # p
    /\ lastRead' = [lastRead EXCEPT ![p][q] = count[q]]
    /\ UNCHANGED count

Next ==
    \E p \in Proc :
        \/ Inc(p)
        \/ Dec(p)
        \/ \E q \in Proc : Read(p, q)

-----------------------------------------------------------------------------
(* Specification with fairness: a process that repeatedly has a legal      *)
(* increment or decrement available eventually performs it.                *)
-----------------------------------------------------------------------------
Fairness ==
    \A p \in Proc :
        /\ SF_vars(Inc(p))
        /\ SF_vars(Dec(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties                                                        *)
-----------------------------------------------------------------------------

\* All counters remain integers
IntegerCounters == \A p \in Proc : count[p] \in Int

\* No counter is ever negative
NonNegative == \A p \in Proc : count[p] >= 0

\* No counter ever reaches or exceeds Max
BelowMax == \A p \in Proc : count[p] < Max

\* Values obtained by reads also respect the bounds
ReadsBounded ==
    \A p, q \in Proc : lastRead[p][q] >= 0 /\ lastRead[p][q] < Max

\* The bound is a fixed natural-number parameter
BoundIsFixedNat == Max \in Nat /\ Max > 0

\* Local operations relate to the global bound: an enabled increment keeps the
\* counter strictly below Max, and an enabled decrement keeps it nonnegative.
IncRespectsBound ==
    \A p \in Proc : ENABLED Inc(p) => count[p] + 1 < Max

DecRespectsBound ==
    \A p \in Proc : ENABLED Dec(p) => count[p] - 1 >= 0

\* Increment is disabled exactly at the upper edge; decrement exactly at zero.
IncDisabledAtBound ==
    \A p \in Proc : (count[p] + 1 >= Max) => ~ENABLED Inc(p)

DecDisabledAtZero ==
    \A p \in Proc : (count[p] = 0) => ~ENABLED Dec(p)

SafetyInvariant ==
    /\ TypeOK
    /\ IntegerCounters
    /\ NonNegative
    /\ BelowMax
    /\ ReadsBounded
    /\ BoundIsFixedNat
    /\ IncRespectsBound
    /\ DecRespectsBound
    /\ IncDisabledAtBound
    /\ DecDisabledAtZero

\* Every step preserves the bounds (action-level safety).
StepPreservesBounds ==
    [][\A p \in Proc : count'[p] >= 0 /\ count'[p] < Max]_vars

\* The parameter Max never changes (it is a constant).
BoundConstant == [][Max' = Max]_vars

-----------------------------------------------------------------------------
(* Liveness properties                                                      *)
-----------------------------------------------------------------------------

\* An increment that is repeatedly enabled is eventually executed.
IncLiveness ==
    \A p \in Proc :
        ([]<>(ENABLED <<Inc(p)>>_vars)) => []<>(<<Inc(p)>>_vars)

\* A decrement that is repeatedly enabled is eventually executed.
DecLiveness ==
    \A p \in Proc :
        ([]<>(ENABLED <<Dec(p)>>_vars)) => []<>(<<Dec(p)>>_vars)

\* If a legal increment is available, the counter eventually changes.
IncProgress ==
    \A p \in Proc : \A n \in CounterRange :
        (count[p] = n /\ n + 1 < Max) ~> (count[p] # n)

\* If a legal decrement is available, the counter eventually changes.
DecProgress ==
    \A p \in Proc : \A n \in CounterRange :
        (count[p] = n /\ n > 0) ~> (count[p] # n)

Liveness == IncLiveness /\ DecLiveness /\ IncProgress /\ DecProgress

-----------------------------------------------------------------------------
THEOREM Spec => []SafetyInvariant
THEOREM Spec => StepPreservesBounds
THEOREM Spec => Liveness
=============================================================================