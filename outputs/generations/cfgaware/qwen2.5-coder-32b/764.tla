------------------------------- MODULE DiningPhilosophers ------------------------------

CONSTANTS N

VARIABLES sem, pc

(*--algorithm DiningPhilosophers
variables sem = [i \in 0..N-1 |-> 1], pc = [i \in 0..N-1 |-> "think"];

process Philosopher \in 0..N-1
begin
    while TRUE do
        if i = 0 then
            await(sem[i] = 1);
            sem[i] := 0;
            await(sem[(i+1) % N] = 1);
            sem[(i+1) % N] := 0;
        else
            await(sem[(i+1) % N] = 1);
            sem[(i+1) % N] := 0;
            await(sem[i] = 1);
            sem[i] := 0;
        end if;
        
        pc[i] := "eat";
        
        sem[i] := 1;
        sem[(i+1) % N] := 1;
        pc[i] := "think";
    end while
end process

end algorithm*)

Spec ==
    /\ Init
    /\ [][Next]_<<pc, sem>>
    /\ WF_pc(Act)

Init == 
    /\ sem = [i \in 0..N-1 |-> 1]
    /\ pc = [i \in 0..N-1 |-> "think"]

Next ==
    \/ \E i \in 0..N-1 : /\ pc' = [pc EXCEPT ![i] = "eat"]
                         /\ sem' = [sem EXCEPT ![i] = 0, ![(i+1) % N] = 0]
    \/ \E i \in 0..N-1 : /\ pc' = [pc EXCEPT ![i] = "think"]
                         /\ sem' = [sem EXCEPT ![i] = 1, ![(i+1) % N] = 1]

Act ==
    { <<i, "eat">> \in 0..N-1 }

WF_pc(action) == 
    /\ \A i \in 0..N-1 : WF_i(pc, action, i)

WF_i(vars, action, i) ==
    \/ vars[i] = "think" -> \E a \in action : a = <<i, "eat">>
    \/ vars[i] = "eat"   -> \A a \in action : a /= <<i, "eat">>

Invariant ==
    /\ \A i \in 0..N-1 : pc[i] = "eat" => pc[(i+1) % N] # "eat"

StarvationFreedom ==
    \/ \A i \in 0..N-1 : <>[]<>(pc[i] = "eat")

=============================================================================