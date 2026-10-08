```
MODULE Counter
EXTENDS Integers

CONSTANTS MaxValue

VARIABLES counter, halted

Init == (counter = 0) /\ (halted = FALSE)

Next == IF halted THEN
            UNCHANGED <<counter, halted>>
        ELSE IF counter < MaxValue THEN
            (* Increment counter and continue *)
            OR [][]
                counter' = counter + 1
                halted' = (counter + 1 = MaxValue)
            UNCHANGED << >>
        ELSE
            (* Halt when counter reaches MaxValue *)
            halted' = TRUE
            UNCHANGED counter

Spec == Init /\ [][Next]_<<counter, halted>>
Termination == <>[]halted
Fairness == WF_vars(Next, <<counter, halted>>)

THEOREM Spec => []Termination
THEOREM Spec => [](counter = 5) => <>(counter /= 5)
THEOREM Spec => [](counter = 9) => <>(counter /= 9)

MaxValue == 10
```
Note: The above TLA+ specification uses the `WF_vars` operator to express weak fairness over the `Next` action with respect to the variables `counter` and `halted`. This ensures that if the incrementing step is continuously enabled, it will eventually execute.