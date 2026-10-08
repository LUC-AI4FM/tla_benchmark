```
MODULE CounterSystem
EXTENDS Integers

CONSTANTS ShortInput, LongInput
VARIABLES counter

Init == (counter = 0)

ShortUpdate == (counter' = Factorial(ShortInput))
LongUpdate == (counter' = Factorial(LongInput))

Next == (ShortUpdate) \/ (LongUpdate)

Spec == Init /\ [][Next]_counter

Factorial(n) == IF n = 0 THEN 1 ELSE n * Factorial(n-1)

TypeInvariant == counter \in {Factorial(ShortInput), Factorial(LongInput)}
Enabled == <>(ShortUpdate) \/ <>(LongUpdate)

THEOREM Spec => []TypeInvariant
THEOREM Spec => <>[]Enabled

Fairness == WF_vars(Next, counter)
```
Note: The `WF_vars` operator is used to specify weak fairness for the `counter` variable with respect to the `Next` action. This ensures that if the system can keep taking steps according to `Next`, it will eventually do so. 

Also note that this specification assumes that `ShortInput` and `LongInput` are constants, e.g., 3 and 9 respectively, as mentioned in the problem description. You should replace these with the actual constant values when instantiating the module.