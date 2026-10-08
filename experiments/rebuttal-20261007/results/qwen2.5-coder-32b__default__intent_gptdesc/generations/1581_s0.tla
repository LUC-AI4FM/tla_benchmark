------------------------------- MODULE DiningPhilosophers -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N >= 2

VARIABLES state

(*--algorithm dining_philosophers
variables 
    state = [p \in 1..N -> "thinking"];

process Philosopher \in 1..N
begin
    while TRUE do
        await state[p] = "thinking";
        state[p] := "hungry";
        
        (* Attempt to pick up left fork *)
        if state[(p-1) % N + 1] \notin {"eating", "hungry"} then
            state[p] := "left_fork_held";
        end if;
        
        await state[p] = "left_fork_held";
        
        (* Attempt to pick up right fork *)
        if state[(p+1) % N + 1] \notin {"eating", "hungry"} then
            state[p] := "eating";
        else
            state[p] := "thinking";  (* Release left fork if right is not available *)
        end if;
        
        await state[p] = "eating";
        state[p] := "thinking";
    end while;
end process;

end algorithm*)

Init == /\ state \in [1..N -> {"thinking"}]

Next ==
    \/ \E p \in 1..N : 
        (state[p] = "thinking" /\ UNCHANGED <<state EXCEPT ![p] = "hungry">>)
    \/ \E p \in 1..N :
        (state[p] = "hungry" /\ state[(p-1) % N + 1] \notin {"eating", "hungry"} /\ 
         UNCHANGED <<state EXCEPT ![p] = "left_fork_held">>)
    \/ \E p \in 1..N :
        (state[p] = "hungry" /\ state[(p-1) % N + 1] \in {"eating", "hungry"} /\ 
         UNCHANGED state)
    \/ \E p \in 1..N :
        (state[p] = "left_fork_held" /\ state[(p+1) % N + 1] \notin {"eating", "hungry"} /\ 
         UNCHANGED <<state EXCEPT ![p] = "eating">>)
    \/ \E p \in 1..N :
        (state[p] = "left_fork_held" /\ state[(p+1) % N + 1] \in {"eating", "hungry"} /\ 
         UNCHANGED <<state EXCEPT ![p] = "thinking">>)
    \/ \E p \in 1..N :
        (state[p] = "eating" /\ UNCHANGED <<state EXCEPT ![p] = "thinking">>)

Spec ==
    Init /\ [][Next]_<<state>>

Safety ==
    /\ \A p \in 1..N : state[p] = "eating" => state[(p-1) % N + 1] \notin {"eating"}
    /\ \A p \in 1..N : state[p] = "eating" => state[(p+1) % N + 1] \notin {"eating"}

MutualExclusion ==
    /\ \A f \in 1..N : Cardinality({p \in 1..N | state[p] \in {"left_fork_held", "eating"} /\ (p-1) % N + 1 = f}) <= 1
    /\ \A f \in 1..N : Cardinality({p \in 1..N | state[p] \in {"left_fork_held", "eating"} /\ (p+1) % N + 1 = f}) <= 1

Liveness ==
    \/ \A p \in 1..N : <>[](state[p] = "eating")
    \/ \A p \in 1..N : <>(\E t \in Nat : state[p] = "hungry" /\ [][Next]_<<state>> /\ state[p] = "eating")

DeadlockFreedom ==
    []<>(\E p \in 1..N : state[p] = "eating")

Fairness ==
    WF_next(Next)

THEOREM Spec => []Safety
THEOREM Spec => []MutualExclusion
THEOREM Spec => Liveness
THEOREM Spec => DeadlockFreedom

=============================================================================