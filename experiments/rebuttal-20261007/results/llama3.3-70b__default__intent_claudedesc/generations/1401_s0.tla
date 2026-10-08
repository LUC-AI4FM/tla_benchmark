```
MODULE CounterExample
EXTENDS Integers

CONSTANTS MaxValue

VARIABLES innerVar, outerVar

InnerModule == INSTANCE Inner WITH var <- innerVar
OuterModule == INSTANCE Outer WITH inner <- innerVar, outer <- outerVar

Init ==
  /\ innerVar = 0
  /\ outerVar = 0

Next ==
  \/ INNER_Next
  \/ (INNER_Unchanged /\ outerVar' = outerVar)

INNER_Next == 
  /\ innerVar < MaxValue
  /\ innerVar' = innerVar + 1
  /\ outerVar' = outerVar

INNER_Unchanged ==
  /\ innerVar' = innerVar
  /\ outerVar' = outerVar

Spec == Init /\ [][Next]_<<innerVar, outerVar>>
           /\ WF_vars(InnerModule!Inner_Next, <<innerVar>>)

THEOREM Spec => <>[] (innerVar = MaxValue)
```

Note: The `Inner` and `Outer` modules are assumed to be defined elsewhere. For completeness, here is a possible definition of these modules:

```
MODULE Inner
EXTENDS Integers

CONSTANTS MaxValue

VARIABLES var

Init == var = 0

Next == 
  \/ var < MaxValue
  /\ var' = var + 1
  \/ var >= MaxValue
  /\ var' = var

Spec == Init /\ [][Next]_var
           /\ WF_vars(Inner_Next, <<var>>)

THEOREM Spec => <>[] (var = MaxValue)
======================================

MODULE Outer
EXTENDS Integers

CONSTANTS MaxValue

VARIABLES inner, outer

Init == 
  /\ inner = 0
  /\ outer = 0

Next == 
  \/ INNER_Next
  \/ (INNER_Unchanged /\ outer' = outer)

INNER_Next == 
  /\ inner < MaxValue
  /\ inner' = inner + 1
  /\ outer' = outer

INNER_Unchanged ==
  /\ inner' = inner
  /\ outer' = outer

Spec == Init /\ [][Next]_<<inner, outer>>
           /\ WF_vars(Inner_Next, <<inner>>)

THEOREM Spec => <>[] (inner = MaxValue)
```