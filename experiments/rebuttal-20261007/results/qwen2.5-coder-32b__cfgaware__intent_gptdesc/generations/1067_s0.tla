------------------------------- MODULE DistributedTerminationDetection -------------------------------
VARIABLES states, terminated

CONSTANTS N

ASSUME N \in Nat /\ N > 0

(*--algorithm DistributedTerminationDetection
variables 
    states = [p \in 1..N -> BOOLEAN],  \* TRUE if process p is active, FALSE otherwise
    terminated = FALSE;                 \* TRUE if termination has been detected

process Process \in 1..N
begin
    while TRUE do
        either
            \* Local decision to deactivate
            await states[self]
            states[self] := FALSE;
        or
            \* Activate another process
            await states[self]
            with p \in 1..N \ {self} do
                states[p] := TRUE;
        or
            \* Termination detection event
            if /\ terminated = FALSE
               /\ \A q \in 1..N : ~states[q]
            then
                terminated := TRUE;
            end if;
        end either;
    end while;
end process;

\* Invariants
Spec ==
    /\ states \in [1..N -> BOOLEAN]
    /\ terminated \in BOOLEAN

\* Safety: Once termination is declared, the system state must indeed be quiescent (no active processes).
Safety ==
    /\ terminated => (\A p \in 1..N : ~states[p])

\* Quiescence Persistence: Once the system reaches the all-inactive state it remains all-inactive thereafter.
QuiescencePersistence ==
    [](terminated => [](\A p \in 1..N : ~states[p]))

\* Liveness: Whenever the system is quiescent, termination detection will eventually be raised.
Liveness ==
    <>(/\ \A p \in 1..N : ~states[p] => <>terminated)

THEOREM Spec => []Safety
THEOREM Spec => QuiescencePersistence
THEOREM Spec => Liveness

end algorithm *)
====================================================================================================