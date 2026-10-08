------------------------------ MODULE Github790 ------------------------------
EXTENDS Naturals, TLC

VARIABLE a

Init == a = 0
Next == (a' = a)
Spec == Init /\ [] [][Next]_<<a>>
AlwaysTrue == <>TRUE => <>[]TRUE

=============================================================================