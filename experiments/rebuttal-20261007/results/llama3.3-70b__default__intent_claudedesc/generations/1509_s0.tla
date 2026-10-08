```
MODULE RecursiveFunction
EXTENDS Integers

CONSTANTS Domain
VARIABLES state

Init == (state \in Domain)

Next == state' = state

Spec == Init /\ [][Next]_state

Inv == state \in {f[x] : x \in Domain}
  where 
    f[x \in Domain] == IF x = 0 THEN 1 ELSE f[x-1] + 2

THEOREM Spec => []Inv
```
Note: The `f` function is defined recursively as follows:
- For the base case, when `x` equals 0, `f[x]` returns 1.
- For other cases, `f[x]` calls itself with the argument `x-1`, and adds 2 to the result. 

This TLA+ module defines a recursive function `f` over the finite domain of integers `Domain`. The system's state variable is initialized within this domain and remains constant. The invariant `Inv` checks whether the state always equals some value produced by the recursive function, ensuring that its initial value is reachable within the function's range.