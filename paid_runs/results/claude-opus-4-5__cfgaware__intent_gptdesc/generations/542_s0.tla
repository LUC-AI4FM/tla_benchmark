---------------------------- MODULE specification ----------------------------

EXTENDS Integers

CONSTANT Workers

VARIABLES counter, state

vars == <<counter, state>>

TypeOK ==
    /\ counter \in Int
    /\ state \in [Workers -> {"ready", "finished"}]

Init ==
    /\ counter = 0
    /\ state = [w \in Workers |-> "ready"]

Increment(w) ==
    /\ state[w] = "ready"
    /\ counter' = counter + 1
    /\ state' = [state EXCEPT ![w] = "finished"]

Idle ==
    /\ \A w \in Workers : state[w] = "finished"
    /\ UNCHANGED vars

Next ==
    \/ \E w \in Workers : Increment(w)
    \/ Idle

Fairness ==
    \A w \in Workers : WF_vars(Increment(w))

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

-----------------------------------------------------------------------------

CounterNeverDecreases ==
    [][counter' >= counter]_vars

CounterIsAlwaysInteger ==
    counter \in Int

IncrementsByOne ==
    [][\A w \in Workers : Increment(w) => counter' = counter + 1]_vars

NoSpontaneousChanges ==
    [][(\E w \in Workers : Increment(w)) \/ UNCHANGED vars]_vars

Safety ==
    /\ []TypeOK
    /\ []CounterIsAlwaysInteger
    /\ CounterNeverDecreases
    /\ IncrementsByOne
    /\ NoSpontaneousChanges

AllFinished ==
    \A w \in Workers : state[w] = "finished"

Termination ==
    <>AllFinished

FinalCounterCorrect ==
    [](AllFinished => counter = Cardinality(Workers))

THEOREM Cardinality(w \in SUBSET Workers) == CHOOSE n \in Int : TRUE

Liveness ==
    /\ Termination
    /\ FinalCounterCorrect

=============================================================================