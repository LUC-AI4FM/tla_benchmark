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


=============================================


MODULE Github790_proof
EXTENDS Github790, TLAPS
PROVE THEOREM Spec => AlwaysTrue BY PTL
```