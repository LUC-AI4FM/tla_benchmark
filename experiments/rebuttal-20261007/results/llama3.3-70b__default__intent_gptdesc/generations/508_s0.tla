```
MODULE SimpleProgram
EXTENDS Integers

CONSTANTS None

VARIABLES x, pc

Init == (x \in 1..10) /\ (pc = "init")

Next == 
  IF pc = "init" THEN 
    (pc' = "assert") /\ (x' = x)
  ELSE IF pc = "assert" THEN 
    ((x * x <= 100)) /\ ((pc' = "term") /\ (x' = x))
  ELSE 
    (pc' = pc) /\ (x' = x)

Spec == Init /\ [][Next]_<<x, pc>>
  
TerminationInvariant == pc = "term"
SafetyProperty == [](x * x <= 100)
TerminationProperty == <>TerminationInvariant

THEOREM Spec => []SafetyProperty
THEOREM Spec => TerminationProperty
```
Note: The `None` constant is declared as per the requirements but not used anywhere in the specification. In a real-world scenario, you would replace this with actual constants if needed or remove it altogether for simplicity.