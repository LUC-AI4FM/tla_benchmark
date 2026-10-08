------------------------------- MODULE DiningPhilosophers ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N
ASSUME N > 1

VARIABLES forks, state

(*--algorithm dining_philosophers

variables forks = [i \in 0..N-1 |-> 1], 
          state = [p \in 0..N-1 |-> "thinking"]

process Philosopher = p \in 0..N-1
begin
    while TRUE do
        if
            /\ p > 0 \/ forks[p] = 1
        then
            await forks[p] = 1;
            forks[p] := 0;
            state[p] := "has_right_fork"
        fi;
        if
            /\ p = 0 \/ forks[(p-1) % N] = 1
        then
            await forks[(p-1) % N] = 1;
            forks[(p-1) % N] := 0;
            state[p] := "eating"
        fi;
        eat:
            assert state[p] = "eating";
            state[p] := "thinking";
            forks[p] := 1;
            forks[(p-1) % N] := 1
    od
end process; *)
    
Init == /\ forks \in [0..N-1 -> {0, 1}]
        /\ state \in [0..N-1 -> {"thinking", "has_right_fork", "eating"}]
        /\ (\A p \in 0..N-1 : state[p] = "thinking" /\ forks[p] = 1)

Next == 
    LET 
        PickRightFork(p) ==
            \/ /\ p > 0
               /\ forks[p] = 1
               /\ state[p] = "thinking"
               /\ forks' = [forks EXCEPT ![p] = 0]
               /\ state' = [state EXCEPT ![p] = "has_right_fork"]
            \/ /\ p = 0
               /\ forks[p] = 1
               /\ state[p] = "thinking"
               /\ forks' = [forks EXCEPT ![p] = 0]
               /\ state' = [state EXCEPT ![p] = "has_right_fork"]
        PickLeftFork(p) ==
            \/ /\ p > 0
               /\ forks[(p-1) % N] = 1
               /\ state[p] = "has_right_fork"
               /\ forks' = [forks' EXCEPT ![(p-1) % N] = 0]
               /\ state' = [state' EXCEPT ![p] = "eating"]
            \/ /\ p = 0
               /\ forks[(p-1) % N] = 1
               /\ state[p] = "has_right_fork"
               /\ forks' = [forks' EXCEPT ![(p-1) % N] = 0]
               /\ state' = [state' EXCEPT ![p] = "eating"]
        Eat(p) ==
            /\ state[p] = "eating"
            /\ state' = [state' EXCEPT ![p] = "thinking"]
            /\ forks' = [forks' EXCEPT ![p] = 1, ![(p-1) % N] = 1]
    IN
        \E p \in 0..N-1 :
            \/ PickRightFork(p)
            \/ PickLeftFork(p)
            \/ Eat(p)

Spec == /\ Init
        /\ [][Next]_<<forks, state>>
        /\ WF_next(<<forks, state>>)

MutualExclusion ==
    \A p, q \in 0..N-1 : p # q => ~ (/\ state[p] = "eating" /\ state[q] = "eating")

StarvationFreedom ==
    \A p \in 0..N-1 :
        <>[][<>(state[p] = "thinking) /\
            <><>(state[p] = "eating")]

================================================================================