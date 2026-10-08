```
MODULE LoopWithFairness
EXTENDS Integers

CONSTANTS Bound
VARIABLES counter, terminated

Init == (counter = 0) /\ (terminated = FALSE)

Next == IF ~terminated THEN
            IF counter < Bound THEN
              (* Increment the counter *)
              OR [||]
                counter' = counter + 1
                terminated' = FALSE
            ELSE
              (* Terminate and remain idle *)
              OR [||]
                counter' = counter
                terminated' = TRUE
            END
          ELSE
            (* Remain in terminated state *)
            OR [||]
              counter' = counter
              terminated' = TRUE

Spec == Init /\ [][Next]_<<counter, terminated>>

THEOREM Spec => []~(counter < 0)
THEOREM Spec => [](counter' = counter + 1) \/ (counter' = counter)

Fairness == WF_vars(Next, <<counter, terminated>>)

Liveness == <>[]terminated
LivenessCheckpoints == <>[](counter = 5)
LivenessFinalStep == <>((counter = 9) /\ (counter' = 10))

THEOREM Spec => Fairness
THEOREM Spec => Liveness
THEOREM Spec => LivenessCheckpoints
THEOREM Spec => LivenessFinalStep

INVARIANT Inv == counter >= 0 /\ counter <= Bound
THEOREM Spec => []Inv
```
Note: The `WF_vars` operator is used to specify weak fairness for the variables in the system, ensuring that if the process remains enabled it eventually makes progress. The `<>[]` and `[]<>` operators are used to express liveness properties, such as eventual termination and the possibility of reaching specific intermediate values.