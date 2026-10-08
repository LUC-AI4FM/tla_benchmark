------------------------------- MODULE DiningPhilosophers -------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N

VARIABLES forks, state

(* --algorithm dining_philosophers
variables 
    forks = [i \in 0..N-1 |-> 1],  (* 1 means fork is available *)
    state = [i \in 0..N-1 |-> "thinking"];  (* states: thinking, hungry, eating *)

process Philosopher \in 0..N-1
begin
    while TRUE do
        await state[self] = "thinking";
        state[self] := "hungry";

        if self = 0 then
            await forks[self] = 1;
            forks[self] := 0;
            await forks[(self - 1) % N] = 1;
            forks[(self - 1) % N] := 0;
        else
            await forks[(self - 1) % N] = 1;
            forks[(self - 1) % N] := 0;
            await forks[self] = 1;
            forks[self] := 0;
        end if;

        state[self] := "eating";

        /\* Eating for a while *\
        state[self] := "thinking";
        
        if self = 0 then
            forks[self] := 1;
            forks[(self - 1) % N] := 1;
        else
            forks[(self - 1) % N] := 1;
            forks[self] := 1;
        end if;
    end while;
end process *********************************************************************)

Init == /\ forks = [i \in 0..N-1 |-> 1]
        /\ state = [i \in 0..N-1 |-> "thinking"]

Next ==
    \/ \E i \in 0..N-1 :
        (state[i] = "thinking" /\
         \/ state' = [state EXCEPT ![i] = "hungry"]
            \/ (/\ state'[i] = "eating"
                /\ forks' = [forks EXCEPT ![i] = 0, ![(i - 1) % N] = 0]
                /\ state' = [state EXCEPT ![i] = "eating"])
        )
    \/ \E i \in 0..N-1 :
        (state[i] = "hungry" /\
         (\A j \in {i, (i - 1) % N} : forks[j] = 1) /\
         state' = [state EXCEPT ![i] = "eating"]
         /\ forks' = [forks EXCEPT ![i] = 0, ![(i - 1) % N] = 0]
        )
    \/ \E i \in 0..N-1 :
        (state[i] = "eating" /\
         state' = [state EXCEPT ![i] = "thinking"]
         /\ forks' = [forks EXCEPT ![i] = 1, ![(i - 1) % N] = 1]
        )

Spec ==
    WF_next(Init, Next) /\
    \A i \in 0..N-1 : SF_next(state[i] = "hungry")

MutualExclusion == \A i, j \in 0..N-1 :
    (i # j) => ~(\E k \in {i, j} : state[k] = "eating")

StarvationFreedom == \A i \in 0..N-1 :
    [](state[i] = "hungry") => <>(state[i] = "eating")
    
=============================================================================