```
MODULE CoffeeCanBeans
EXTENDS Integers
CONSTANTS MaxBeans
VARIABLES beans

Init == (beans = [black |-> 0, white |-> 0] /\ 
         beans[black] + beans[white] <= MaxBeans)

TwoBlack == (beans[black] >= 2) /\ 
             (beans' = [black |-> beans[black] - 2, white |-> beans[white] + 1])

TwoWhite == (beans[white] >= 2) /\ 
            (beans' = [black |-> beans[black] + 1, white |-> beans[white] - 2])

OneEach == (beans[black] > 0 /\ beans[white] > 0) /\ 
           (beans' = [black |-> beans[black] - 1, white |-> beans[white] - 1])

Stutter == (beans = beans') /\ (beans[black] + beans[white] = 1)

Next == TwoBlack \/ TwoWhite \/ OneEach \/ Stutter

Spec == Init /\ [][Next]_beans

TypeInvariant == beans \in [black : Int, white : Int]

MonotonicDecrease == beans[black] + beans[white] <= beans'[black] + beans'[white]

EventualTermination == WF_vars(Stutter)

ParityLoopInvariant == IF (beans[white] % 2 = 0) THEN beans[white]' % 2 = 1 ELSE beans[white]' % 2 = 0

Hypothesis == (Init /\ Spec) => ((beans[black] + beans[white] = 1) => 
                                IF (beans[white] % 2 = 0) THEN beans[black] > 0 ELSE beans[white] > 0)

THEOREM Hypothesis
PROOF OMITTED
```