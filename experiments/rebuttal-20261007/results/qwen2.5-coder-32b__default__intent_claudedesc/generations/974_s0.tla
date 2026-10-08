------------------------------- MODULE SharedMemoryAlgorithm -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES sharedRegisters, localRegisters, states

(* --algorithm SharedMemoryAlgorithm
variables 
    sharedRegisters = [i \in 1..N -> 0],
    localRegisters = [i \in 1..N -> 0],
    states = [i \in 1..N -> "idle"]
begin
    while TRUE do
        await states[self] = "idle";
        states[self] := "writing";
        sharedRegisters[self] := 1;
        states[self] := "written";
        localRegisters[self] := sharedRegisters[(self - 1) % N + 1];
        states[self] := "idle"
    end while
end algorithm *)

Init == /\ sharedRegisters = [i \in 1..N -> 0]
        /\ localRegisters = [i \in 1..N -> 0]
        /\ states = [i \in 1..N -> "idle"]

WriteStep(i) ==
    /\ states[i] = "idle"
    /\ states' = [states EXCEPT ![i] = "writing"]
    /\ sharedRegisters' = [sharedRegisters EXCEPT ![i] = 1]
    /\ localRegisters' = localRegisters

CompleteWriteStep(i) ==
    /\ states[i] = "writing"
    /\ states' = [states EXCEPT ![i] = "written"]
    /\ sharedRegisters' = sharedRegisters
    /\ localRegisters' = localRegisters

ReadStep(i) ==
    /\ states[i] = "written"
    /\ states' = [states EXCEPT ![i] = "idle"]
    /\ sharedRegisters' = sharedRegisters
    /\ localRegisters' = [localRegisters EXCEPT ![i] = sharedRegisters[(i - 1) % N + 1]]

Next ==
    \/ \E i \in 1..N : WriteStep(i)
    \/ \E i \in 1..N : CompleteWriteStep(i)
    \/ \E i \in 1..N : ReadStep(i)

Spec == Init /\ [][Next]_<<sharedRegisters, localRegisters, states>>

(* Fairness *)
WFStates ==
    WF_next(states, "idle")

(* Safety Property *)
Safety ==
    \A s \in States: (\E i \in 1..N: s.localRegisters[i] = 1) => (\E j \in 1..N: s.states[j] = "idle")

(* Inductive Invariant *)
InductiveInvariant ==
    /\ sharedRegisters \in [1..N -> {0, 1}]
    /\ localRegisters \in [1..N -> {0, 1}]
    /\ states \in [1..N -> {"idle", "writing", "written"}]
    /\ (\A i \in 1..N: states[i] = "idle" => sharedRegisters[i] = 0)
    /\ (\A i \in 1..N: states[i] = "writing" => sharedRegisters[i] \in {0, 1})
    /\ (\A i \in 1..N: states[i] = "written" => sharedRegisters[i] = 1)

SpecWithFairness ==
    Spec /\ WFStates

THEOREM SpecWithFairness => []Safety
================================================================================