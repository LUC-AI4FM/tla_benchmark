------------------------------- MODULE DiningPhilosophers -------------------------------
CONSTANTS N

VARIABLES forks, state

(*--algorithm dining_philosophers

variables 
    forks = [i \in 0..N-1 |-> 1],  (* 1 means fork is available *)
    state = [i \in 0..N-1 |-> "thinking"];  (* states: thinking, hungry, eating *)

process Philosopher \in 0..N-1
begin
    while TRUE do
        think:
            if state[self] = "thinking" then
                state[self] := "hungry";
            end if;
        
        pick_up_forks:
            if self = 0 then
                await forks[self] = 1; 
                forks[self] := 0;
                await forks[(self + N - 1) % N] = 1; 
                forks[(self + N - 1) % N] := 0;
            else
                await forks[self] = 1; 
                forks[self] := 0;
                await forks[(self + 1) % N] = 1; 
                forks[(self + 1) % N] := 0;
            end if;
        
        eat:
            if state[self] = "hungry" and forks[self] = 0 and forks[(self + 1) % N] = 0 then
                state[self] := "eating";
            end if;

        put_down_forks:
            if state[self] = "eating" then
                forks[self] := 1;
                forks[(self + 1) % N] := 1;
                state[self] := "thinking";
            end if;
    end while;
end process

end algorithm*)

Spec ==
    /\ Init
    /\ [][Next]_<<phil>>
    /\ WF_phil(Next)

Init ==
    /\ forks = [i \in 0..N-1 |-> 1]
    /\ state = [i \in 0..N-1 |-> "thinking"]

Next ==
    \/ \E i \in 0..N-1 : phil[i] \/UNCHANGED <<forks, EXCEPT state[i] := "hungry">>
    \/ \E i \in 0..N-1 : (i = 0 /\ forks[i] = 1 /\ forks[(i + N - 1) % N] = 1) 
        \/UNCHANGED <<EXCEPT forks[i] := 0, forks[(i + N - 1) % N] := 0>>
    \/ \E i \in 0..N-1 : (i /= 0 /\ forks[i] = 1 /\ forks[(i + 1) % N] = 1) 
        \/UNCHANGED <<EXCEPT forks[i] := 0, forks[(i + 1) % N] := 0>>
    \/ \E i \in 0..N-1 : (state[i] = "hungry" /\ forks[i] = 0 /\ forks[(i + 1) % N] = 0)
        \/UNCHANGED <<EXCEPT state[i] := "eating">>
    \/ \E i \in 0..N-1 : (state[i] = "eating")
        \/UNCHANGED <<forks, EXCEPT state[i] := "thinking", forks[i] := 1, forks[(i + 1) % N] := 1>>

phil == [i \in 0..N-1 |-> \/ state[i] = "hungry" /\ (i = 0 /\ forks[i] = 1 /\ forks[(i + N - 1) % N] = 1)
                                   \/ (i /= 0 /\ forks[i] = 1 /\ forks[(i + 1) % N] = 1)]

Invariant ==
    \A i \in 0..N-1 : state[i] \in {"thinking", "hungry", "eating"}
    /\ \A i \in 0..N-1 : (state[i] = "eating" => forks[i] = 0 /\ forks[(i + 1) % N] = 0)
    /\ \/ \E i \in 0..N-1 : state[i] = "eating"
       \/ \A i \in 0..N-1 : state[i] /= "eating" => \A j \in 0..N-1 : forks[j] = 1

WF_phil ==
    WF_vars(phil, <<forks, state>>)

=============================================================================