MODULE TwoComponentSystem
EXTENDS Naturals, Sequences

CONSTANTS initSeq, newVal

VARIABLES seq, result

vars == <<seq, result>>

Init ==
    /\ seq = initSeq
    /\ result = 0

serviceEnabled == (result = 0)

serviceAction ==
    /\ result = 0
    /\ result' = newVal
    /\ seq' = Filter(seq, lambda x: x # newVal)

outerStutter ==
    /\ ~serviceEnabled
    /\ UNCHANGED <<seq, result>>

Next ==
    \/ serviceAction
    \/ outerStutter

Spec == Init /\ [][Next]_vars /\ WF_vars(serviceAction)

Invariant1 == result \in {0, newVal}

Invariant2 == (result = 0 /\ seq = initSeq) \/ 
              (result = newVal /\ seq = Filter(initSeq, lambda x: x # newVal))

Safety == [] (Invariant1 /\ Invariant2)

EventuallyStable == <> (result = newVal /\ seq = Filter(initSeq, lambda x: x # newVal))