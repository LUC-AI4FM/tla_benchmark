---------------------------- MODULE HourClock12 ----------------------------
EXTENDS Naturals

CONSTANT MaxTicks        \* Bound used only by the model-checking state constraint

ASSUME MaxTicks \in Nat

VARIABLES
    hr,          \* Current hour, an integer in 0..11
    mark,        \* Ghost: hour value at the last reference point (Init or last Set)
    ticks,       \* Ghost: number of successive ticks since the last reference point
    lastEvent    \* Ghost: record describing the most recent atomic event

vars == <<hr, mark, ticks, lastEvent>>

Hours == 0..11

EventKinds == {"init", "tick", "set"}

Event == [kind : EventKinds, prev : Hours, val : Hours]

\* Pure model of n successive ticks starting from h
RECURSIVE TickN(_, _)
TickN(h, n) == IF n = 0 THEN h ELSE TickN((h + 1) % 12, n - 1)

-----------------------------------------------------------------------------
\* Initial condition: the clock starts at any value in 0..11 (not fixed)

Init ==
    /\ hr \in Hours
    /\ mark = hr
    /\ ticks = 0
    /\ lastEvent = [kind |-> "init", prev |-> hr, val |-> hr]

-----------------------------------------------------------------------------
\* Events: each event is a single atomic update of the clock

\* Normal tick: advance the hour by one modulo 12
Tick ==
    /\ hr' = (hr + 1) % 12
    /\ mark' = mark
    /\ ticks' = ticks + 1
    /\ lastEvent' = [kind |-> "tick", prev |-> hr, val |-> (hr + 1) % 12]

\* External set: replace the current hour with any allowed value v
Set(v) ==
    /\ v \in Hours
    /\ hr' = v
    /\ mark' = v
    /\ ticks' = 0
    /\ lastEvent' = [kind |-> "set", prev |-> hr, val |-> v]

\* Ticks and sets are chosen non-deterministically; concurrent environment
\* requests are serialized into a sequence of atomic events.
Next ==
    \/ Tick
    \/ \E v \in Hours : Set(v)

\* Weak fairness on Tick guarantees ticks are never permanently prevented
Spec == Init /\ [][Next]_vars /\ WF_vars(Tick)

-----------------------------------------------------------------------------
\* Safety invariants

TypeOK ==
    /\ hr \in Hours
    /\ mark \in Hours
    /\ ticks \in Nat
    /\ lastEvent \in Event

\* Safety: the clock value is always within 0..11
RangeOK == hr \in Hours

\* Ticks are never disabled: a tick is possible in every reachable state
TickAlwaysEnabled == ENABLED Tick

\* Deterministic wrap-around (pure cycle property of the tick function):
\* 12 successive ticks return to the start, and no fewer than 12 do.
CycleLemma ==
    \A h \in Hours :
        /\ TickN(h, 12) = h
        /\ \A k \in 1..11 : TickN(h, k) # h

\* Deterministic wrap-around (behavioral): after k uninterrupted ticks from
\* the reference point, the clock equals mark advanced by k mod 12; in
\* particular after every 12 successive ticks the clock is back at mark.
WrapAround ==
    /\ hr = (mark + ticks) % 12
    /\ hr = TickN(mark, ticks % 12)
    /\ (ticks % 12 = 0) => (hr = mark)

\* Set consistency: right after a set, the clock equals the written value
SetConsistency ==
    (lastEvent.kind = "set") => (hr = lastEvent.val)

\* No lost updates: the current value always reflects the most recent event
NoLostUpdate ==
    /\ hr = lastEvent.val
    /\ (lastEvent.kind = "tick") => (hr = (lastEvent.prev + 1) % 12)

Invariants ==
    /\ TypeOK
    /\ RangeOK
    /\ TickAlwaysEnabled
    /\ CycleLemma
    /\ WrapAround
    /\ SetConsistency
    /\ NoLostUpdate

-----------------------------------------------------------------------------
\* Action (step) properties

\* Every tick step advances the hour by exactly one modulo 12
TickStepCorrect ==
    [][ Tick => hr' = (hr + 1) % 12 ]_vars

\* Every set step yields exactly the written value immediately afterwards
SetStepCorrect ==
    [][ \A v \in Hours : Set(v) => hr' = v ]_vars

\* Under serial execution, the value after each event is the one that event
\* produced, so of two sequential events the second one determines the result
SerialLastWriterWins ==
    [][ hr' = lastEvent'.val ]_vars

\* The clock never leaves the valid range on any step
RangePreserved ==
    [][ hr' \in Hours ]_vars

-----------------------------------------------------------------------------
\* Liveness properties

\* Progress: the clock value changes infinitely often
Progress == []<><<TRUE>>_hr

\* Ticks are never permanently disabled: tick steps occur infinitely often
TicksRecur == []<><<Tick>>_vars

\* From any state, the clock eventually takes a different value
EventuallyChanges == \A h \in Hours : [](hr = h => <>(hr # h))

-----------------------------------------------------------------------------
\* Model-checking helper: bounds the ghost tick counter for TLC

StateConstraint == ticks <= MaxTicks

-----------------------------------------------------------------------------
THEOREM Spec => []Invariants
THEOREM Spec => TickStepCorrect /\ SetStepCorrect /\ SerialLastWriterWins /\ RangePreserved
THEOREM Spec => Progress /\ TicksRecur /\ EventuallyChanges

=============================================================================