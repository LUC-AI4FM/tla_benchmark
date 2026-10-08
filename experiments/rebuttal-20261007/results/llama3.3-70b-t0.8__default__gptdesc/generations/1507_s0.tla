```
MODULE Clock
EXTENDS Integers

CONSTANTS

VARIABLES clock

Check(p) == IF p THEN TRUE ELSE FALSE

Flip(b) == ~b

TypeOK == clock \in {TRUE, FALSE}

Init == (* TLC will not check the coverage of this recursive call *)
        Check(clock = TRUE)

Constraint == clock = TRUE

Next == clock' = Flip(clock)

Spec == Init /\ [][Next]_clock

THEOREM Spec => []TypeOK
THEOREM Spec => <>Constraint
```
Note: The above specification uses the `~` operator for logical negation, which is a standard TLA+ operator. Also note that in a real-world scenario, you would typically use a more descriptive name instead of `Check` and `Flip`, but I have kept them as per your request to maintain consistency with the problem description.