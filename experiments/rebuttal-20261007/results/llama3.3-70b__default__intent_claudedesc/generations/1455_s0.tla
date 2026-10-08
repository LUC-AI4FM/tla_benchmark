```
MODULE SubsetOfPowerset
EXTENDS Integers, FiniteSets, Naturals

CONSTANTS None

VARIABLES testResult

Init ==
  testResult = 
    (SUBSET Power({1, 2}) \subseteq Power({1, 2, 3})) /\
    ~(Power({1, 2, 3}) \subseteq Power({1, 2})) /\
    (SUBSET Power({1, 2}) \subseteq Power({1, 2, 3})) /\
    (SUBSET Power( {}) \subseteq Power({1, 2, 3})) /\
    ~(Power({1, 2, 3}) \subseteq Power( {})) /\
    (SUBSET Power({1}) \subseteq Power(Nat)) /\
    (SUBSET Power({1}) \subseteq Power(Int))

Next ==
  UNCHANGED testResult

Spec == Init /\ [][Next]_testResult

THEOREM Spec => []testResult
THEOREM Spec => testResult \in BOOLEAN
```