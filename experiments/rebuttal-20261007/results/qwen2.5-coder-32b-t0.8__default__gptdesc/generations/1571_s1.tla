---------------------------- MODULE DiningPhilosophers ----------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N

VARIABLES forks, state

(* --algorithm dining_philosophers
variables 
    forks = [i \in 0..N-1 |-> 1],
    state = [i \in 0..N-1 |-> "thinking"];

process (phi \in 0..N-1) \in Philosopher
begin
    while TRUE do
        if phi > 0 then
            await forks[phi] = 1;
            forks[phi] := 0;
            await forks[(phi - 1) % N] = 1;
            forks[(phi - 1) % N] := 0;
        else
            await forks[(phi + 1) % N] = 1;
            forks[(phi + 1) % N] := 0;
            await forks[phi] = 1;
            forks[phi] := 0;
        end if;
        state[phi] := "eating";
        state[phi] := "thinking";
        forks[phi] := 1;
        if phi > 0 then
            forks[(phi - 1) % N] := 1;
        else
            forks[(phi + 1) % N] := 1;
        end if;
    end while;
end process;

begin
end algorithm *)

Init == 
    /\ forks = [i \in 0..N-1 |-> 1]
    /\ state = [i \in 0..N-1 |-> "thinking"]

Next == 
    \/ \/ phi \in 0..N-1 : 
        (/\ state[phi] = "thinking"
         /\ IF phi > 0 THEN forks[phi] = 1 ELSE forks[(phi + 1) % N] = 1 ENDIF
         /\ LET right_fork = IF phi > 0 THEN phi ELSE (phi + 1) % N ENDLET
            IN \E s \in SUBSET {i \in 0..N-1 : i # phi /\ i # right_fork} :
                forks' = [forks EXCEPT ![right_fork] = 0]
                /\ state' = [state EXCEPT ![phi] = "waiting"]
                /\ UNCHANGED (EXCEPT forks[right_fork], state[phi])
         )
        \/ (/\ state[phi] = "waiting"
            /\ IF phi > 0 THEN forks[(phi - 1) % N] = 1 ELSE forks[phi] = 1 ENDIF
            /\ LET left_fork = IF phi > 0 THEN (phi - 1) % N ELSE phi ENDLET
               right_fork = IF phi > 0 THEN phi ELSE (phi + 1) % N ENDLET
               IN \E s \in SUBSET {i \in 0..N-1 : i # phi /\ i # left_fork} :
                   forks' = [forks EXCEPT ![left_fork] = 0]
                   /\ state' = [state EXCEPT ![phi] = "eating"]
                   /\ UNCHANGED (EXCEPT forks[left_fork], forks[right_fork], state[phi])
           )
        \/ (/\ state[phi] = "eating"
            /\ forks' = [forks EXCEPT ![phi] = 1, ![IF phi > 0 THEN (phi - 1) % N ELSE (phi + 1) % N ENDIF] = 1]
            /\ state' = [state EXCEPT ![phi] = "thinking"]
            /\ UNCHANGED (EXCEPT forks[phi], forks[IF phi > 0 THEN (phi - 1) % N ELSE (phi + 1) % N ENDIF], state[phi])
           )
    \/ UNCHANGED <<forks, state>>

Spec == 
    Init /\ [][Next]_<<forks, state>> /\ WF_<<phil \in 0..N-1 |-> Philosopher(phil)>>_<<forks, state>>

MutualExclusion == \A phi1, phi2 \in 0..N-1 : phi1 # phi2 => ~[]<>(state[phi1] = "eating" /\ state[phi2] = "eating")

StarvationFreedom == 
    \A phi \in 0..N-1 : [](<>[](state[phi] = "thinking) => <>[](state[phi] = "eating"))

THEOREM Spec => []MutualExclusion
THEOREM Spec => []StarvationFreedom

=============================================================================