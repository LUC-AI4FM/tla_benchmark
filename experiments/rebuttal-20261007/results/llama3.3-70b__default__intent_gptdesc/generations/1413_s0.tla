```
MODULE PersistentTautologyDetector
EXTENDS Integers, TLC

CONSTANTS InitialValue

VARIABLES state

Init == state = InitialValue

Next == state' = state

Spec == Init /\ [][Next]_state

THEOREM Spec => []<>[]state = InitialValue

TemporalTheorem == 
  [](<<state = TRUE>>_state => <>[]<<state = TRUE>>_state)

THEOREM Spec => TemporalTheorem
```