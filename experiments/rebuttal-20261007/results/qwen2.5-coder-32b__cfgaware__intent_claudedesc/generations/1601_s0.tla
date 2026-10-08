------------------------------- MODULE FischerMutex -------------------------------

CONSTANTS N, Epsilon, Delta

VARIABLES lock, timers, criticalSection

(*--algorithm fischer_mutex
variables 
    lock = 0,
    timers = [p \in 1..N -> 0],
    criticalSection = {}
;

process (P \in 1..N)
begin
    while TRUE do
        await(lock = 0);
        timers[P] := Delta;
        lock := P;
        timers[P] := Epsilon;
        await(timers[P] = 0 /\ lock = P);
        criticalSection := criticalSection \cup {P};
        (* Critical Section *)
        criticalSection := criticalSection \ {P};
        lock := 0
    end while
end process;

process Clock
begin
    while TRUE do
        if (\A p \in 1..N : timers[p] > 0) then
            timers' := [timers EXCEPT ![p] = timers[p] - 1];
        else
            timers' := timers;
        end if
    end while
end process;

end algorithm;*)

Spec == /\ Init
        /\ \A p \in 1..N : SpecProc(p)
        /\ SpecClock

Init == /\ lock = 0
      /\ timers = [p \in 1..N -> 0]
      /\ criticalSection = {}

SpecProc(p) == 
    \/ /\ lock = 0
       /\ timers' = [timers EXCEPT ![p] = Delta]
       /\ lock' = p
       /\ timers' = [timers' EXCEPT ![p] = Epsilon]
       /\ UNCHANGED criticalSection
    \/ /\ timers[p] > 0
       /\ timers' = [timers EXCEPT ![p] = timers[p] - 1]
       /\ UNCHANGED lock
       /\ UNCHANGED criticalSection
    \/ /\ timers[p] = 0
       /\ lock = p
       /\ criticalSection' = criticalSection \cup {p}
       /\ UNCHANGED lock
       /\ UNCHANGED timers
    \/ /\ criticalSection = {p}
       /\ criticalSection' = {}
       /\ lock' = 0
       /\ UNCHANGED timers

SpecClock ==
    \/ /\ (\A p \in 1..N : timers[p] > 0)
       /\ timers' = [timers EXCEPT ![p] = timers[p] - 1 FORALL p \in 1..N]
       /\ UNCHANGED lock
       /\ UNCHANGED criticalSection
    \/ /\ (\E p \in 1..N : timers[p] = 0)
       /\ timers' = timers
       /\ UNCHANGED lock
       /\ UNCHANGED criticalSection

Invariant == 
    /\ \/ lock = 0
         \/ (\E p \in 1..N : lock = p /\ timers[p] > 0)
    /\ Cardinality(criticalSection) <= 1

Liveness ==
    \A p \in 1..N : <>(criticalSection = {p})

=============================================================================