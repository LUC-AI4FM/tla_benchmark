```
MODULE SimpleStateMachine
EXTENDS Integers

CONSTANTS None

VARIABLES state

Init == (state = 0)

Next == (* state is even and between 0 and 9 *)
        /\ state' \in {s \in 0..9 : s % 2 = 0}
        /\ (state = state' ∨ state' = state + 2 ∨ state' = state - 2)

Spec == Init ∧ [][Next]_state

THEOREM Spec => []((state \in 0..9) ∧ (state % 2 = 0))
```
Note: The `None` in the `CONSTANTS` declaration is used because TLA+ requires at least one constant or variable to be declared. Since there are no specific constants mentioned in the problem description, we use `None`. 

Also note that this specification does not explicitly define how the state changes (e.g., it doesn't specify what happens when the state reaches 8 and needs to increase), as per the request to focus on safety properties without implementation details. The `Next` action allows for stuttering steps or increments/decrements by 2, ensuring that if a step is taken, the new state remains within the specified bounds and parity.