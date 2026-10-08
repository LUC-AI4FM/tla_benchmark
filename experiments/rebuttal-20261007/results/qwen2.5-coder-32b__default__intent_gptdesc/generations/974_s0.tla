------------------------------- MODULE ConcurrentProcesses -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N \* Number of processes

VARIABLES 
    registers, \* Shared registers
    localStorages, \* Local storages
    pc \* Program counters

Init == /\ registers = [p \in 1..N -> {0}]
        /\ localStorages = [p \in 1..N -> 0]
        /\ pc = [p \in 1..N -> "beginWrite"]

Next ==
    \/ \E p \in 1..N : 
        /\ pc[p] = "beginWrite"
        /\ registers' = [registers EXCEPT ![p] = {0, 1}]
        /\ localStorages' = localStorages
        /\ pc' = [pc EXCEPT ![p] = "completeWrite"]
    \/ \E p \in 1..N : 
        /\ pc[p] = "completeWrite"
        /\ registers' = [registers EXCEPT ![p] = {1}]
        /\ localStorages' = localStorages
        /\ pc' = [pc EXCEPT ![p] = "readNeighbor"]
    \/ \E p \in 1..N : 
        /\ pc[p] = "readNeighbor"
        /\ LET leftNeighbor == IF p = 1 THEN N ELSE p - 1
           neighborValue == CHOOSE v \in registers[leftNeighbor] : TRUE
        IN localStorages' = [localStorages EXCEPT ![p] = neighborValue]
        /\ registers' = registers
        /\ pc' = [pc EXCEPT ![p] = "terminated"]

Spec ==
    /\ Init
    /\ [][Next]_<<pc>>
    /\ WF_next(<<pc>>)

SafetyInvariant ==
    \A p \in 1..N : 
        \/ pc[p] = "terminated"
        \/ (registers[p] \subseteq {0, 1} /\ registers[p] /= {})

TypeInvariant ==
    /\ \A p \in 1..N : registers[p] \subseteq {0, 1}
    /\ \A p \in 1..N : localStorages[p] \in {0, 1}
    /\ \A p \in 1..N : pc[p] \in {"beginWrite", "completeWrite", "readNeighbor", "terminated"}

LivenessProperty ==
    <>(\A p \in 1..N : pc[p] = "terminated") => <>(\E p \in 1..N : localStorages[p] = 1)

CompleteSpec ==
    /\ Spec
    /\ SafetyInvariant
    /\ TypeInvariant
    /\ LivenessProperty

=============================================================================