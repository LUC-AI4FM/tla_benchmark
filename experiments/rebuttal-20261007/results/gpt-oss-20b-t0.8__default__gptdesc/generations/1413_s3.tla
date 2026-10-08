```
--- Module: Github790 ----------------------------------------------
MODULE Github790
VARIABLES a

Init == a = 0
Next == a' = a

Spec == Init /\ [] [ Next ]_a

AlwaysTrue == <>TRUE => <>[]TRUE
END MODULE

--- Module: Github790_proof -----------------------------------------
MODULE Github790_proof
EXTENDS Github790, TLAPS

THEOREM AlwaysTrueThm == AlwaysTrue
END MODULE
```