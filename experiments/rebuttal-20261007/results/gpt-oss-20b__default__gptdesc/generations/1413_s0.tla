MODULE Github790
VARIABLES a

Init == a = 0

Next == a' = a

Spec == Init /\ []Next

AlwaysTrue == <> TRUE => <> [] TRUE


MODULE Github790_proof
EXTENDS Github790, TLAPS

THEOREM AlwaysTrue_Proof == Spec => AlwaysTrue
  BY PTL