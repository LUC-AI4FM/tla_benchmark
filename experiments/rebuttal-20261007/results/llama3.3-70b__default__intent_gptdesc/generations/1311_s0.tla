```
MODULE GCDAlgorithm
EXTENDS Integers

CONSTANTS MaxValue, FirstInput
VARIABLES SecondInput, CurrentGcd, Done

Init ==
  /\ SecondInput \in 1..MaxValue
  /\ CurrentGcd = [FirstInput, SecondInput]_2
  /\ Done = FALSE

Next ==
  IF ~Done THEN
    IF CurrentGcd[1] > CurrentGcd[2]
    THEN
      CurrentGcd' = [CurrentGcd[1] - CurrentGcd[2], CurrentGcd[2]]
    ELSE
      CurrentGcd' = [CurrentGcd[2] - CurrentGcd[1], CurrentGcd[1]]
    Done' = (CurrentGcd[1] = 0) \/ (CurrentGcd[2] = 0)
  ELSE
    UNCHANGED <<CurrentGcd, Done>>

Spec == Init /\ [][Next]_<<CurrentGcd, Done>>
  
Termination ==
  <>(Done)

SafetyInvariant ==
  [](CurrentGcd[1] >= 0 /\ CurrentGcd[2] >= 0
   /\ (CurrentGcd[1] = 0 \/ CurrentGcd[2] = 0) => (CurrentGcd[1] + CurrentGcd[2]) = GCD(FirstInput, SecondInput)
   /\ GCD(CurrentGcd[1], CurrentGcd[2]) = GCD(FirstInput, SecondInput))

THEOREM Spec => []SafetyInvariant
THEOREM Spec => Termination

Fairness == SF_VARIABLES(Done)

GCD(a, b) == IF a = 0 THEN b ELSE GCD(b % a, a)
```