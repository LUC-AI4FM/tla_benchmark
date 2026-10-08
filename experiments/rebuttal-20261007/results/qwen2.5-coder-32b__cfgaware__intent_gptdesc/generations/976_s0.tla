------------------------------- MODULE RingProcesses -------------------------------

CONSTANTS N \* Number of processes

VARIABLES reg, res, state \* reg[i] is the local shared register of process i
                           \* res[i] is the result register of process i
                           \* state[i] is the control state of process i (0: before first step, 1: between steps, 2: terminated)

\* Control states
CONSTANT BEFORE_FIRST_STEP == 0
CONSTANT BETWEEN_STEPS     == 1
CONSTANT TERMINATED         == 2

\* Initial predicate
Init == /\ reg = [i \in 1..N -> 0]
        /\ res = [i \in 1..N -> 0]
        /\ state = [i \in 1..N -> BEFORE_FIRST_STEP]

\* Next-state relation for a single process
NextProc(i) ==
    \/ /\ state[i] = BEFORE_FIRST_STEP
       /\ reg' = [reg EXCEPT ![i] = 1]
       /\ res' = res
       /\ state' = [state EXCEPT ![i] = BETWEEN_STEPS]
    \/ /\ state[i] = BETWEEN_STEPS
       /\ reg' = reg
       /\ res' = [res EXCEPT ![i] = reg[(i - 1) % N + 1]]
       /\ state' = [state EXCEPT ![i] = TERMINATED]

\* Next-state relation for the system
Next ==
    \E i \in 1..N : \/ /\ state[i] # TERMINATED
                       /\ NextProc(i)
                       /\ \A j \in (1..N) \ {i} :
                          /\ reg'[j] = reg[j]
                          /\ res'[j] = res[j]
                          /\ state'[j] = state[j]

\* Specification
Spec == Init /\ [][Next]_<<reg, res, state>>

\* Type invariants
TypeOK ==
    /\ \A i \in 1..N : \/ reg[i] \in {0, 1}
                         /\ res[i] \in {0, 1}
                         /\ state[i] \in {BEFORE_FIRST_STEP, BETWEEN_STEPS, TERMINATED}

\* Inductive invariant
Inv ==
    /\ TypeOK
    /\ \A i \in 1..N : \/ state[i] = TERMINATED
                        \/ (\E j \in 1..N : state[j] = BEFORE_FIRST_STEP)

\* Safety property: whenever every process has terminated, at least one process’s result register equals 1.
Safety ==
    /\ \A i \in 1..N : state[i] = TERMINATED
    -> (\E i \in 1..N : res[i] = 1)

\* Liveness condition: it is possible for all processes to eventually reach the terminated state under fair scheduling
Termination ==
    <>(\A i \in 1..N : state[i] = TERMINATED)

\* Correctness specification
PCorrect == Spec /\ []Inv /\ []TypeOK /\ <>Safety

=============================================================================