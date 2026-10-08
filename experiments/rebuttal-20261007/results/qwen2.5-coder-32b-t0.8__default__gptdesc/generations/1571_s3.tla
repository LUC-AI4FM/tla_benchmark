------------------------------- MODULE DiningPhilosophers -------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N

VARIABLES forks, philosophersState

(* --algorithm dining_philosophers

variables 
    forks = <<1 \in Nat : i \in 0 .. N-1 >>,
    philosophersState = << "thinking" \in STRING : i \in 0 .. N-1 >>;

process Philosopher = i \in 0 .. N-1
begin
    while TRUE do
        if i = 0 then
            await forks[i] > 0;
            atomic { forks[i] := forks[i] - 1; }
            await forks[(i+1) % N] > 0;
            atomic { forks[(i+1) % N] := forks[(i+1) % N] - 1; }
        else
            await forks[(i+1) % N] > 0;
            atomic { forks[(i+1) % N] := forks[(i+1) % N] - 1; }
            await forks[i] > 0;
            atomic { forks[i] := forks[i] - 1; }
        end if;
        philosophersState[i] := "eating";
        philosophersState[i] := "thinking";
        atomic { forks[i] := forks[i] + 1; }
        atomic { forks[(i+1) % N] := forks[(i+1) % N] + 1; }
    od;
end process

end algorithm *)

Init == /\ forks = <<1 \in Nat : i \in 0 .. N-1 >>
        /\ philosophersState = << "thinking" \in STRING : i \in 0 .. N-1 >>

Next ==
    LET
        PhilAct(i) ==
            CASE philosophersState[i] = "thinking" /\
                 (i = 0 -> forks[i] > 0 /\ forks[(i+1) % N] > 0
                  ELSE forks[(i+1) % N] > 0 /\ forks[i] > 0) ->
                IF i = 0 THEN
                    /\ forks' = [forks EXCEPT ![i] = forks[i] - 1, ![ (i+1) % N ] = forks[ (i+1) % N ] - 1]
                    /\ philosophersState' = [philosophersState EXCEPT ![i] = "eating"]
                ELSE
                    /\ forks' = [forks EXCEPT ![ (i+1) % N ] = forks[ (i+1) % N ] - 1, ![i] = forks[i] - 1]
                    /\ philosophersState' = [philosophersState EXCEPT ![i] = "eating"]
                ENDIF
            [] philosophersState[i] = "eating" ->
                /\ forks' = [forks EXCEPT ![i] = forks[i] + 1, ![(i+1) % N] = forks[ (i+1) % N ] + 1]
                /\ philosophersState' = [philosophersState EXCEPT ![i] = "thinking"]
            [] TRUE -> UNCHANGED <<forks, philosophersState>>
    IN
        \E i \in 0 .. N-1 : PhilAct(i)

Spec ==
    Init /\ [][Next]_<<philosophersState, forks>> /\
    WF_<<philosophersState, forks>>(\A i \in 0 .. N-1: PhilAct(i))

MutualExclusion == \A i, j \in 0 .. N-1 :
                         i # j => philosophersState[i] = "eating" => philosophersState[j] # "eating"

StarvationFreedom ==
    \A i \in 0 .. N-1 : <>[](philosophersState[i] = "thinking") /\ <>(philosophersState[i] = "eating")

Invariant == MutualExclusion

THEOREM Spec => []Invariant

THEOREM Spec => StarvationFreedom

=============================================================================