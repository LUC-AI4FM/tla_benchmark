```
MODULE EuclidAlgorithm
VARIABLES pc, u, v, v_ini

Init == (pc = "Start") ∧ (u = 24) ∧ (v_ini \in 1..N) ∧ (v = v_ini)

Next == IF pc = "Start" THEN
            pc' = "Loop" ∧ u' = u ∧ v' = v ∧ v_ini' = v_ini
          ELSE IF pc = "Loop" THEN
            IF u > v THEN
              pc' = "Loop" ∧ u' = u - v ∧ v' = v ∧ v_ini' = v_ini
            ELSE IF u < v THEN
              pc' = "Loop" ∧ u' = u ∧ v' = v - u ∧ v_ini' = v_ini
            ELSE
              pc' = "Done" ∧ u' = u ∧ v' = v ∧ v_ini' = v_ini
          ELSE
            pc' = pc ∧ u' = u ∧ v' = v ∧ v_ini' = v_ini

Spec == Init ∧ [][Next]_<<pc, u, v, v_ini>> ∧ WF_<<pc, u, v, v_ini>>(Next)

Termination == <> (pc = "Done")

THEOREM Spec => Termination
```
Note: The `WF` operator is used to specify weak fairness of the `Next` action. This ensures that if the system can take a step according to `Next`, it will eventually do so. 

Also note that this specification uses the `<< >>` notation to specify the variables that are changed by the `Next` action, which allows for stuttering steps where none of these variables change. The `_` symbol is used as a placeholder for the tuple of variables being primed.

The `THEOREM` statement at the end asserts that the specification implies termination, meaning that if the system follows the specified behavior, it will eventually reach the "Done" state. 

Please ensure to define constant `N` before using this module in your model-checking configuration.