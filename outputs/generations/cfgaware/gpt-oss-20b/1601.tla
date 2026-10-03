------------------------------ MODULE FischerTimed ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS N, Epsilon, Delta
(* Sentinel value for timers *)
CONSTANT Infinity

VARIABLES state, timer

RELEASED == "released"
WAITING   == "waiting"
CRITICAL  == "critical"

Init ==
    /\ state = [i \in 1..N |-> RELEASED]
    /\ timer = [i \in 1..N |-> 0]

\* NOTE: This specification intentionally contains a timing‑sensitive bug.
\* When N > 1 and Delta >= Epsilon, the invariant may be violated.

\*--algorithm FischerTimed
variables state, timer

process i in 1..N do
    while TRUE do
        state[i] := WAITING;
        timer[i] := Delta;
        await ( \A j \in 1..N : (j # i) => state[j] # CRITICAL ) /\ (timer[i] > 0);
        if timer[i] = 0 then
            state[i] := RELEASED
        else
            state[i] := CRITICAL;
            (* critical section placeholder *)
            state[i] := RELEASED
        fi
    end while
end process

process Tick do
    while TRUE do
        timer := [i \in 1..N |-> IF timer[i] > 0 THEN timer[i]-1 ELSE timer[i]];
        await FALSE;
    end while
end process
\*--end algorithm

Spec == Init /\ [] [][Next]_vars

Invariant ==
    \A i, j \in 1..N : ~(state[i] = CRITICAL /\ state[j] = CRITICAL)

Liveness ==
    [] <> (\E i \in 1..N : state[i] = CRITICAL)

=============================================================================