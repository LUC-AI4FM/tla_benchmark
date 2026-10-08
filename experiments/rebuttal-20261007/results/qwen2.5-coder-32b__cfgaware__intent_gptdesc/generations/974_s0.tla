------------------------------- MODULE ConcurrentProcesses -------------------------------

CONSTANTS N \* Number of processes

VARIABLES 
    registers, \* Shared registers
    localStorages, \* Local storage for each process
    pcs \* Program counters for each process

\* Control states for the protocol
Consts == << "write", "completeWrite", "read", "terminated" >>

\* Initial predicate
Init == 
    /\ registers = [p \in 1..N -> {0}]
    /\ localStorages = [p \in 1..N -> 0]
    /\ pcs = [p \in 1..N -> "write"]

\* Next-state relation for a single process
NextProc(p) ==
    LET left == IF p = 1 THEN N ELSE p - 1 IN
    CASE pcs[p] = "write" ->
        /\ registers' = [registers EXCEPT ![p] = {0, 1}]
        /\ localStorages' = localStorages
        /\ pcs' = [pcs EXCEPT ![p] = "completeWrite"]
    [] pcs[p] = "completeWrite" ->
        /\ registers' = [registers EXCEPT ![p] = {1}]
        /\ localStorages' = localStorages
        /\ pcs' = [pcs EXCEPT ![p] = "read"]
    [] pcs[p] = "read" ->
        /\ registers' = registers
        /\ localStorages' = [localStorages EXCEPT ![p] = CHOOSE v \in registers[left]]
        /\ pcs' = [pcs EXCEPT ![p] = "terminated"]
    [] pcs[p] = "terminated" ->
        /\ registers' = registers
        /\ localStorages' = localStorages
        /\ pcs' = pcs

\* Next-state relation for all processes
Next ==
    \E p \in 1..N : 
        \/ /\ NextProc(p)
           /\ \A q \in (1..N) \ {p} :
                /\ registers' = registers
                /\ localStorages' = localStorages
                /\ pcs'[q] = pcs[q]
        \/ /\ registers' = registers
           /\ localStorages' = localStorages
           /\ pcs' = pcs

\* Specification
Spec == Init /\ [][Next]_<<registers, localStorages, pcs>>

\* Safety property: if all processes terminate, at least one process must have read the value 1
Safety ==
    [](\/ p \in 1..N : pcs[p] = "terminated") => (\/ p \in 1..N : localStorages[p] = 1)

\* Progress/termination property: it is possible for all processes to eventually terminate
PCorrect == <>(/\ p \in 1..N : pcs[p] = "terminated")

\* Type invariants
TypeOK ==
    /\ registers \in [1..N -> SUBSET {0, 1}]
    /\ localStorages \in [1..N -> {0, 1}]
    /\ pcs \in [1..N -> Consts]

\* Invariant: shared registers always hold a nonempty subset of {0,1}, local storages hold 0 or 1, and process program counters are within the defined control states
Inv ==
    /\ TypeOK
    /\ (\A p \in 1..N : registers[p] /= {})

=============================================================================