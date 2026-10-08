MODULE Github790
VARIABLE a

Init == a = 0
Next == a' = a

Spec == Init /\ [][Next]_a

AlwaysTrueProp == <>TRUE => <>[]TRUE
=============================================================================

MODULE Github790_proof
EXTENDS Github790, TLAPS

THEOREM AlwaysTrue : AlwaysTrueProp
=============================================================================