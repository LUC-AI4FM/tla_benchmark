MODULE LambdaTest

EXTENDS Integers, TLC

CONSTANTS 
    Const1,
    Const2

VARIABLES 
    Var1,
    Var2

Init == TRUE

Next == TRUE

Spec == Init /\ [][Next]_<<Var1, Var2>>

ASSUME \E x \in {1, 2, 3} : (LAMBDA y : y + x)(1) = x + 1
ASSUME \A x \in {1, 2, 3} : (LAMBDA y : y * x)(2) = x * 2

VARIABLES TestVar

INSTANCE TLCWith <<LAMBDA x : x + Const1>>, <<LAMBDA x : x * Const2>> WITH TestVar <- Var1

PrintT("Testing lambda expressions")
PrintT((LAMBDA x : x + 5)(3) = 8)
PrintT((LAMBDA x : x * 4)(3) = 12)

====