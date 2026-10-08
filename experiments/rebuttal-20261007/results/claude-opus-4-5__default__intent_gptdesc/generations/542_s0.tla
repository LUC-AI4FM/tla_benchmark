---------------------------- MODULE TwoWorkers ----------------------------

EXTENDS Integers

CONSTANTS W1, W2

VARIABLES counter, state

Workers == {W1, W2}

TypeOK ==
    /\ counter \in Int
    /\ state \in [Workers -> {"ready", "finished"}]

Init ==
    /\ counter = 0
    /\ state = [w \in Workers |-> "ready"]

WorkerIncrement(w) ==
    /\ state[w] = "ready"
    /\ counter' = counter + 1
    /\ state' = [state EXCEPT ![w] = "finished"]

Idle ==
    /\ \A w \in Workers : state[w] = "finished"
    /\ UNCHANGED <<counter, state>>

Next ==
    \/ WorkerIncrement(W1)
    \/ WorkerIncrement(W2)
    \/ Idle

Spec == Init /\ [][Next]_<<counter, state>> 
        /\ WF_<<counter, state>>(WorkerIncrement(W1))
        /\ WF_<<counter, state>>(WorkerIncrement(W2))

\* Safety: Counter never decreases
CounterNeverDecreases ==
    [][counter' >= counter]_<<counter, state>>

\* Safety: Counter is always a non-negative integer bounded appropriately
CounterInRange ==
    counter \in 0..2

\* Safety: Each worker increment increases counter by exactly one
IncrementsByOne ==
    [][\A w \in Workers : 
        WorkerIncrement(w) => counter' = counter + 1]_<<counter, state>>

\* Safety: Counter only changes when a worker performs increment
CounterOnlyChangesOnIncrement ==
    [][counter' # counter => 
        \E w \in Workers : 
            /\ state[w] = "ready" 
            /\ state'[w] = "finished"]_<<counter, state>>

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeOK
    /\ CounterInRange
    /\ counter = Cardinality({w \in Workers : state[w] = "finished"})

Cardinality(S) == 
    IF S = {} THEN 0
    ELSE IF S = {W1} THEN 1
    ELSE IF S = {W2} THEN 1
    ELSE IF S = {W1, W2} THEN 2
    ELSE 0

\* Liveness: Both workers eventually finish
BothWorkersTerminate ==
    <>(state[W1] = "finished" /\ state[W2] = "finished")

\* Liveness: Each worker eventually finishes
Worker1Terminates == <>(state[W1] = "finished")
Worker2Terminates == <>(state[W2] = "finished")

\* Final counter equals number of finished workers (equals 2 when both done)
FinalCounterCorrect ==
    []((\A w \in Workers : state[w] = "finished") => counter = 2)

\* Termination state invariant
Terminated ==
    /\ state[W1] = "finished"
    /\ state[W2] = "finished"
    /\ counter = 2

==========================================================================