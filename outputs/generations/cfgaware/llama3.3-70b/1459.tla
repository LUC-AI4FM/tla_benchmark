```
MODULE SmallTransitionSystem
VARIABLE x

Init == (x = 0)
Next == (x < 3) => (x' = x + 1) /\ (x >= 3) => (x' = x)

Spec == Init /\ [][Next]_x

Limit == 10
```
Note: The `Limit` constant is defined as required, but its value does not affect the behavior of this specification. In a real-world scenario, you would replace `10` with the actual limit value relevant to your system or model checking configuration.