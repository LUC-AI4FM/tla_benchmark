```
MODULE SimpleConcurrentSystem
EXTENDS Integers

CONSTANTS ConstantValue
VARIABLES IncrementingComponent, UnchangedComponent

Init ==
  /\ IncrementingComponent \in 0..100
  /\ UnchangedComponent \in {1, 2, 3}
  /\ ConstantValue = 42

Next ==
  /\ IncrementingComponent' = IF IncrementingComponent < 100 THEN IncrementingComponent + 1 ELSE IncrementingComponent
  /\ UnchangedComponent' = UnchangedComponent
  /\ ConstantValue' = ConstantValue

Spec == Init /\ [][Next]_<<IncrementingComponent, UnchangedComponent, ConstantValue>>

THEOREM Spec => []<>(IncrementingComponent = 100)
THEOREM Spec => [](UnchangedComponent' = UnchangedComponent)
THEOREM Spec => [](ConstantValue' = ConstantValue)

WF_Vars == <<IncrementingComponent, UnchangedComponent, ConstantValue>>
Enable_Increment == (IncrementingComponent < 100)

Fairness == WF_Vars(Next) /\ SF_Vars(Next)

Inv ==
  /\ IncrementingComponent \in 0..100
  /\ UnchangedComponent \in {1, 2, 3}
  /\ ConstantValue = 42

THEOREM Spec => []Inv
THEOREM Spec => <>[](IncrementingComponent = 100)
THEOREM Spec => [](Enable_Increment => <>(IncrementingComponent' = IncrementingComponent + 1))
```