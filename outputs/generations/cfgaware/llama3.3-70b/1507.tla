```
MODULE TinySystem
VARIABLE clock

Check(p) == IF p THEN TRUE ELSE FALSE

Flip(b) == IF b THEN FALSE ELSE TRUE

TypeOK == clock \in BOOLEAN

Init == 
  (* TLC will not check this recursive call *)
  Check(clock = FALSE)
  /\ clock = FALSE

Next == clock' = Flip(clock)

THEOREM Spec => []TypeOK
```
Note: The `Spec` in the theorem is implicitly defined as `Init /\ [][Next]_clock`, which means that the system starts in an initial state and always takes a next step according to the `Next` predicate. This is a common pattern in TLA+ specifications, but it's not explicitly written out here because it's implied by the structure of the module.