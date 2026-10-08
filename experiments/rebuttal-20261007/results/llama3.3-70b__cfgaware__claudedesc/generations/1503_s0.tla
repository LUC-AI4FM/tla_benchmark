```
MODULE F
VARIABLE x

Op(S, P, Q) == {s \in S : P(s) /\ Q(s, TRUE)}

Init == x \in Op({1, 2, 3, 4, 5}, LAMBDA s : s > 1, LAMBDA s, b : (s % 2 ≠ 0) /\ b)

Next == UNCHANGED x

THEOREM Spec == Init /\ [][Next]_x
```
Note: The `Spec` theorem is not strictly necessary for the module to be valid, but it's a common way to define the overall specification in TLA+. If you want to omit it, you can simply remove the last line.