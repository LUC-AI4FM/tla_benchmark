------------------------------- MODULE MainModule -------------------------------
EXTENDS Integers, TLC

CONSTANTS A, B

VARIABLES x, y

ConstOp == 5

INSTANCE SecondModule WITH var1 <- ConstOp

Init == /\ x = 0
        /\ y = 0

Next == \/ /\ x' = x + 1
             /\ UNCHANGED <<y>>
          \/ /\ y' = y + 1
             /\ UNCHANGED <<x>>

Spec == Init /\ [][Next]_<<x, y>>

=============================================================================