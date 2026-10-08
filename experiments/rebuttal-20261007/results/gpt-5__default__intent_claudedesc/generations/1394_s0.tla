------------------------------ MODULE Main ------------------------------
EXTENDS Naturals, TLC

VARIABLES x, z

K == 10

M == INSTANCE SubModule WITH
  a <- x,
  b <- K,
  c <- z

Init == M!Init
Next == M!Next

Spec == Init /\ [][Next]_<<x, z>>

TypeInv == /\ x \in {0, 1}
           /\ z \in {100, 200}

THEOREM Spec => []TypeInv
=============================================================================