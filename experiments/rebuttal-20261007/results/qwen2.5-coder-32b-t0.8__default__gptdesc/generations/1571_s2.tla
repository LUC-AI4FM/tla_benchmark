---------------------------- MODULE DiningPhilosophers ----------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N

VARIABLES forks, state

(*--algorithm DiningPhilosophers

variables forks = [i \in 0..N-1 |-> 1], state = [i \in 0..N-1 |-> "thinking"];

process Philosopher \in 0..N-1
begin
    while TRUE do
        if i = 0 then
            await(forks[i] = 1);
            forks[i] := 0;
            await(forks[(i + N - 1) % N] = 1);
            forks[(i + N - 1) % N] := 0;
        else
            await(forks[(i + N - 1) % N] = 1);
            forks[(i + N - 1) % N] := 0;
            await(forks[i] = 1);
            forks[i] := 0;
        end if;

        state[i] := "eating";
        
        state[i] := "thinking";

        if i = 0 then
            forks[i] := 1;
            forks[(i + N - 1) % N] := 1;
        else
            forks[(i + N - 1) % N] := 1;
            forks[i] := 1;
        end if;
    end while
end process

end algorithm *)

Init == /\ forks = [i \in 0..N-1 |-> 1]
        /\ state = [i \in 0..N-1 |-> "thinking"]

AcquireForks(i) == 
    \/ /\ i # 0
       /\ forks[(i + N - 1) % N] = 1
       /\ forks[i] = 1
       /\ forks' = [forks EXCEPT ![i] = 0, ![(i + N - 1) % N] = 0]
    \/ /\ i = 0
       /\ forks[i] = 1
       /\ forks[(i + N - 1) % N] = 1
       /\ forks' = [forks EXCEPT ![i] = 0, ![(i + N - 1) % N] = 0]

ReleaseForks(i) == 
    \/ /\ i # 0
       /\ forks' = [forks EXCEPT ![i] = 1, ![(i + N - 1) % N] = 1]
    \/ /\ i = 0
       /\ forks' = [forks EXCEPT ![i] = 1, ![(i + N - 1) % N] = 1]

Next == 
    \E i \in 0..N-1 :
        \/ /\ state[i] = "thinking"
           /\ AcquireForks(i)
           /\ state' = [state EXCEPT ![i] = "eating"]
        \/ /\ state[i] = "eating"
           /\ ReleaseForks(i)
           /\ state' = [state EXCEPT ![i] = "thinking"]

Spec == Init /\ [][Next]_<<f>> \A i \in 0..N-1: WF_<<f>>(PhiloFair(i))

PhiloFair(i) == 
    \/ i # 0
       -> <> (/\ state[i] = "thinking"
             /\ forks[(i + N - 1) % N] = 1
             /\ forks[i] = 1)
    \/ i = 0
       -> <> (/\ state[i] = "thinking"
             /\ forks[i] = 1
             /\ forks[(i + N - 1) % N] = 1)

MutualExclusion == \A i, j \in 0..N-1: i # j => ~(\E k \in 0..N-1: state[k] = "eating" /\ (k = i \/ k = j))

StarvationFreedom ==
    \A i \in 0..N-1:
        <> (/\ state[i] = "thinking"
            /\ forks[(i + N - 1) % N] = 1
            /\ forks[i] = 1)

=============================================================================