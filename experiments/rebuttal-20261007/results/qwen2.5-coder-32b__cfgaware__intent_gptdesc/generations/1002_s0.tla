------------------------------- MODULE BarrierSync -------------------------------

CONSTANTS N \* Number of processes

ASSUME N > 0

VARIABLES phase, arrivedCount, round

\* Phase constants
CONSTANT PHASE_PRE_BARRIER = "pre_barrier"
CONSTANT PHASE_POST_BARRIER = "post_barrier"

\* Type invariants
TypeOK == 
    /\ phase \in [1..N -> {PHASE_PRE_BARRIER, PHASE_POST_BARRIER}]
    /\ arrivedCount \in 0..N
    /\ round \in Nat

\* Initial predicate
Init ==
    /\ phase = [i \in 1..N |-> PHASE_PRE_BARRIER]
    /\ arrivedCount = 0
    /\ round = 0

\* Next-state relation for a single process arriving at the barrier
Arrive(i) ==
    /\ phase[i] = PHASE_PRE_BARRIER
    /\ phase' = [phase EXCEPT ![i] = PHASE_POST_BARRIER]
    /\ arrivedCount' = arrivedCount + 1
    /\ round' = IF arrivedCount + 1 = N THEN round ELSE round

\* Next-state relation for a single process being released from the barrier
Release(i) ==
    /\ phase[i] = PHASE_POST_BARRIER
    /\ arrivedCount = N
    /\ phase' = [phase EXCEPT ![i] = PHASE_PRE_BARRIER]
    /\ arrivedCount' = IF i = 1 THEN 0 ELSE arrivedCount \* Only one process resets the count
    /\ round' = IF i = 1 THEN round + 1 ELSE round

\* Next-state relation for any process
Next ==
    \/ \E i \in 1..N : Arrive(i)
    \/ \E i \in 1..N : Release(i)

\* Specification of the system
Spec == Init /\ [][Next]_<<phase, arrivedCount, round>>

\* Barrier safety property: no process may be released until all have arrived
Safety ==
    []<>(arrivedCount = N => \A i \in 1..N : phase[i] = PHASE_POST_BARRIER)

\* Barrier liveness property: if all processes arrive, they will eventually be released
Liveness ==
    [](arrivedCount = N => <>[](\E i \in 1..N : phase[i] = PHASE_PRE_BARRIER))

\* Combined barrier property
BarrierProperty == Safety /\ Liveness

=============================================================================