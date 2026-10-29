---- MODULE TwoWorkerIncrement ----
EXTENDS Naturals

Workers == {1, 2}

VARIABLES counter, pc

vars == <<counter, pc>>

TypeOK ==
    /\ counter \in Nat
    /\ pc \in [Workers -> {"ready", "done"}]

Init ==
    /\ counter = 0
    /\ pc = [w \in Workers |-> "ready"]

Increment(w) ==
    /\ pc[w] = "ready"
    /\ counter' = counter + 1
    /\ pc' = [pc EXCEPT ![w] = "done"]

Terminating ==
    /\ \A w \in Workers : pc[w] = "done"
    /\ UNCHANGED vars

Next ==
    \/ \E w \in Workers : Increment(w)
    \/ Terminating

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A w \in Workers : WF_vars(Increment(w))

Finished == {w \in Workers : pc[w] = "done"}

Card2(S) == IF S = {} THEN 0 ELSE IF S = Workers THEN 2 ELSE 1

CounterIsInt == counter \in Nat

CounterMatchesFinished == counter = Card2(Finished)

FinalCorrect ==
    (\A w \in Workers : pc[w] = "done") => counter = 2

CounterNeverDecreases == [][counter' >= counter]_vars

StepIncrementsByOne ==
    [][\A w \in Workers : (pc[w] = "ready" /\ pc'[w] = "done") => counter' = counter + 1]_vars

OnlyWorkerChanges ==
    [][ (counter' # counter) => (\E w \in Workers : Increment(w)) ]_vars

Termination == <>(\A w \in Workers : pc[w] = "done")

EventuallyCounterTwo == <>[](counter = 2)

====