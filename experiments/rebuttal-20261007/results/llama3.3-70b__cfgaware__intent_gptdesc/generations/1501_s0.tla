```
MODULE Spec
VARIABLES counter

ConstantFactorial3 == 6
ConstantFactorial9 == 362880

ShortUpdate(counter) ==
  counter' = ConstantFactorial3

LongUpdate(counter) ==
  counter' = ConstantFactorial9

Next == \/ ShortUpdate(counter)
          \/ LongUpdate(counter)

Spec == counter = 0 /\ [][Next]_counter

THEOREM Spec => []((counter = ConstantFactorial3) \/ (counter = ConstantFactorial9))
THEOREM Spec => <>[]<>(ShortUpdate(counter)) 
THEOREM Spec => <>[]<>(LongUpdate(counter))
```
Note: The `ConstantFactorial3` and `ConstantFactorial9` are defined as the factorial of 3 and 9 respectively. 

The `ShortUpdate` and `LongUpdate` operators define the two possible updates to the counter.

The `Next` operator defines the next state relation, which is a disjunction of the short and long updates.

The `Spec` operator defines the overall behavior of the system as all executions starting from the initial state (counter = 0) and taking only the permitted transitions.

The first theorem states that the counter is always equal to one of the concrete factorial values produced by those computations.

The second and third theorems state liveness expectations: the system does not deadlock and executions may choose either kind of update indefinitely.