MODULE Github790

VARIABLE a

Init == a = 0

Next == a' = a

Spec == Init /\ [] Next

AlwaysTrue == <> TRUE => <> [] TRUE

=============================================================================

MODULE Github790_proof
EXTENDS Github790, TLAPS

THEOREM AlwaysTrue:
  Spec => AlwaysTrue

================================================================================