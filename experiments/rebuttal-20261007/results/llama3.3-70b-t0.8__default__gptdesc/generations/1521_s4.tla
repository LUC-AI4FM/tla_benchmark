```
MODULE CoffeeCanBeanProblem
EXTENDS Integers

CONSTANTS MaxBeans
VARIABLES beans

Init ==
  /\ beans = [black |-> 0, white |-> 0]
  /\ beans.black \in 0..MaxBeans
  /\ beans.white \in 0..MaxBeans

Next ==
  \/ RemoveTwoBlackBeans
  \/ RemoveTwoWhiteBeans
  \/ RemoveOneOfEach
  \/ TerminationStuttering

RemoveTwoBlackBeans ==
  /\ beans.black >= 2
  /\ beans' = [beans EXCEPT !.black = @ - 2]

RemoveTwoWhiteBeans ==
  /\ beans.white >= 2
  /\ beans' = [beans EXCEPT !.white = @ - 2]

RemoveOneOfEach ==
  /\ beans.black > 0
  /\ beans.white > 0
  /\ beans' = [beans EXCEPT !.black = @ - 1, !.white = @ - 1]

TerminationStuttering ==
  /\ (beans.black + beans.white) = 1
  /\ beans' = beans

Spec == Init /\ [][Next]_beans

TypeInvariant ==
  /\ beans \in [black : Int, white : Int]
  /\ beans.black >= 0
  /\ beans.white >= 0

MonotonicDecrease ==
  TotalBeans' <= TotalBeans

TotalBeans == beans.black + beans.white

WeakFairness ==
  WF_vars(<<RemoveTwoBlackBeans, RemoveTwoWhiteBeans, RemoveOneOfEach>>)

EventualTermination ==
  <>(beans.black + beans.white) = 1

ParityInvariant ==
  (beans.white % 2) = (InitBeans.white % 2)

InitBeans == Init.beans

Hypothesis ==
  (InitBeans.white % 2) = 0 => (beans.black > 0 /\ beans.white = 0)
  (InitBeans.white % 2) # 0 => (beans.black = 0 /\ beans.white > 0)

THEOREM Spec => []TypeInvariant
THEOREM Spec => []MonotonicDecrease
THEOREM Spec => EventualTermination
THEOREM Spec => []ParityInvariant
THEOREM Spec => Hypothesis

```
Note: This specification uses the `Integers` module for integer arithmetic and assumes that the `MaxBeans` constant is defined elsewhere. The `WF_vars` operator is used to specify weak fairness conditions.