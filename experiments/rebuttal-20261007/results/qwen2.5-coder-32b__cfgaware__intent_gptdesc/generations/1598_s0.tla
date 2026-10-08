------------------------------- MODULE MutualExclusion -------------------------------
VARIABLES tour1, tour2, intents, states

CONSTANTS N \* Number of processes

(*--algorithm mutual_exclusion
variables 
    tour1 = 0,
    tour2 = 0,
    intents = [p \in 1..N -> FALSE],
    states = [p \in 1..N -> "idle"];

process (P \in 1..N)
begin
Entry:
    while TRUE do
        intents[P] := TRUE;
        tour1 := P;
        await(tour2 = 0);
        tour2 := P;

        \* Wait for all other processes to clear their intent flags
        with q \in 1..N \ {P} do
            while intents[q] do skip;

        \* Check if it's this process's turn
        if tour1 = P /\ tour2 = P then
            states[P] := "critical_section";
            \* Critical section code here
            states[P] := "idle";

            \* Cleanup shared state
            tour2 := 0;
        else
            \* Abort and retry
            intents[P] := FALSE;
            await(tour1 # P);
        end if;
    end while;
end process;

end algorithm*)

Spec == /\ Init
        /\ [][Next]_<<tour1, tour2, intents, states>>

Init == /\ tour1 = 0
      /\ tour2 = 0
      /\ intents \in [1..N -> BOOLEAN]
      /\ states \in [1..N -> {"idle", "critical_section"}]

Next ==
    \/ \E p \in 1..N : intents' = [intents EXCEPT ![p] = TRUE]
                        /\ tour1' = p
                        /\ tour2' = 0
                        /\ UNCHANGED states
    \/ \E p \in 1..N : tour2 = 0
                        /\ tour2' = p
                        /\ UNCHANGED intents
                        /\ UNCHANGED states
    \/ \E p \in 1..N, q \in 1..N \ {p} : intents[q]
                                      /\ intents' = [intents EXCEPT ![q] = FALSE]
                                      /\ UNCHANGED tour1
                                      /\ UNCHANGED tour2
                                      /\ UNCHANGED states
    \/ \E p \in 1..N : tour1 = p /\ tour2 = p
                        /\ states' = [states EXCEPT ![p] = "critical_section"]
                        /\ UNCHANGED intents
                        /\ UNCHANGED tour1
                        /\ UNCHANGED tour2
    \/ \E p \in 1..N : states[p] = "critical_section"
                        /\ states' = [states EXCEPT ![p] = "idle"]
                        /\ tour2' = 0
                        /\ UNCHANGED intents
                        /\ UNCHANGED tour1
    \/ \E p \in 1..N : intents[p]
                        /\ tour1 # p
                        /\ intents' = [intents EXCEPT ![p] = FALSE]
                        /\ UNCHANGED states
                        /\ UNCHANGED tour1
                        /\ UNCHANGED tour2

Invariant ==
    /\ tour1 \in 0..N
    /\ tour2 \in 0..N
    /\ intents \in [1..N -> BOOLEAN]
    /\ states \in [1..N -> {"idle", "critical_section"}]
    /\ \/ tour2 = 0
       \/ \A p, q \in 1..N : p # q => states[p] # "critical_section" \/ states[q] # "critical_section"

Liveness ==
    WF_next(<<tour1, tour2, intents, states>>) /\
    SF_next(states)

WF_next(vars) == \A p \in 1..N : WFair(Next, vars, P = p)
SF_next(vars) == SFair(Next, vars, \E p \in 1..N : states[p] = "critical_section")

=============================================================================