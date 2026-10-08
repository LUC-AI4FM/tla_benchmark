---- MODULE CounterStrategy ----

CONSTANTS Prisoner, p2, p3

VARIABLES switches, visitedCount, declaredCompletion

(* --algorithm CounterStrategy
variables 
    switches = <<FALSE, FALSE>>,  \* Initial state of the switches is arbitrary (FALSE or TRUE)
    visitedCount = 0,
    declaredCompletion = FALSE;

process CounterPrisoner = "Counter"
begin
    while ~declaredCompletion do
        await \E i \in {1, 2} : switches[i] = TRUE;
        with (i \in {1, 2} |-> switches[i] = TRUE) do
            visitedCount := visitedCount + 1;
            if visitedCount >= CARDINALITY(Prisoner) - 1 then
                declaredCompletion := TRUE;
            end if;
            switches[i] := FALSE;
        end with;
    end while;
end process;

process NonCounterPrisoners = "NonCounter"
variables 
    mySwitch = CHOOSE i \in {1, 2} : TRUE;  \* Each non-counter chooses a switch to flip
begin
    while ~declaredCompletion do
        await switches[mySwitch] = FALSE;
        with (mySwitch |-> switches[mySwitch] = FALSE) do
            switches[mySwitch] := TRUE;
        end with;
    end while;
end process;

end algorithm *)

Spec == 
    /\ TYPEOK
    /\ \/ declaredCompletion
       \/ \A i \in {1, 2} : ~switches[i]
    /\ CountInvariant
    /\ Safety
    /\ Liveness

TYPEOK ==
    /\ switches \in [1..2 -> BOOLEAN]
    /\ visitedCount \in 0..(CARDINALITY(Prisoner) - 1)
    /\ declaredCompletion \in BOOLEAN

CountInvariant ==
    \/ declaredCompletion
    \/ visitedCount < CARDINALITY(Prisoner)

Safety ==
    declaredCompletion => (\A p \in Prisoner \ {p2} : \E i \in {1, 2} : switches[i] = TRUE)

Liveness ==
    <>[] declaredCompletion

====