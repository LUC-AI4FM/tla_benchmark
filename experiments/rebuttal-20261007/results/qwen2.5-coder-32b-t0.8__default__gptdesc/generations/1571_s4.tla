------------------------------- MODULE DiningPhilosophers -------------------------------
EXTENDS Naturals, TLC

CONSTANTS N

VARIABLES forks, state

(* --algorithm DiningPhilosophers
variables 
    forks = [i \in 0..N-1 |-> 1],  (* 1 means free, 0 means taken *)
    state = [i \in 0..N-1 |-> "thinking"];

process Philosopher \in 0..N-1
begin
    while TRUE do
        if i = 0 then
            await forks[i] = 1;
            forks[i] := 0;
            await forks[(i + N - 1) \% N] = 1;
            forks[(i + N - 1) \% N] := 0;
        else
            await forks[(i + N - 1) \% N] = 1;
            forks[(i + N - 1) \% N] := 0;
            await forks[i] = 1;
            forks[i] := 0;
        end if;
        
        state[i] := "eating";
        
        state[i] := "thinking";
        
        forks[i] := 1;
        forks[(i + N - 1) \% N] := 1;
    end while
end process *****************************************************************)

Init == 
    /\ forks = [i \in 0..N-1 |-> 1]
    /\ state = [i \in 0..N-1 |-> "thinking"]

AcquireForks(i) ==
    \/ i = 0 -> 
        \/ /\ forks[i] = 1
           /\ forks[(i + N - 1) \% N] = 1
    \/ /\ forks[(i + N - 1) \% N] = 1
       /\ forks[i] = 1

ReleaseForks(i) ==
    /\ forks' = [forks EXCEPT ![i] = 1, ![ (i + N - 1) \% N ] = 1]
    /\ state' = [state EXCEPT ![i] = "thinking"]

Next == 
    \E i \in 0..N-1 : 
        \/ /\ AcquireForks(i)
           /\ forks' = [forks EXCEPT ![i] = 0, ![ (i + N - 1) \% N ] = 0]
           /\ state' = [state EXCEPT ![i] = "eating"]
        \/ /\ state[i] = "eating"
           /\ ReleaseForks(i)

Spec == 
    /\ Init
    /\ [][Next]_<<forsome i \in 0..N-1 >> philosopher_i

(* Safety: Mutual exclusion *)
MutualExclusion ==
    \A i, j \in 0..N-1 : i # j => ~(\E k \in 0..N-1 : state[k] = "eating" /\ (k = i \/ k = j))

(* Liveness: Starvation freedom *)
StarvationFreedom ==
    \A i \in 0..N-1 : <<forsome i >> philosopher_i

 fairnessAssumption ==
    WF_(Next, {i \in 0..N-1}) philosopher_i
=============================================================================