```
MODULE Github790
EXTENDS Integers
CONSTANTS 
VARIABLES a

Init == (a = 0)
Next == (a' = a)

Spec == Init /\ [][Next]_a
AlwaysTrue == <>TRUE => <>[]TRUE

THEOREM Spec => AlwaysTrue


=============================================================================
MODULE Github790_proof
EXTENDS Github790, TLAPS
THEOREM AlwaysTrue
PROOF
PTL
QED
```
Note: The above TLA+ module uses the SANY syntax and is designed to be parsed by the SANY parser. The `THEOREM` statement in the first module is a statement of a theorem to be proven, while the second module actually proves this theorem using the PTL backend.