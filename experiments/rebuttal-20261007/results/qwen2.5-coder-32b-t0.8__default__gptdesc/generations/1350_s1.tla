---- MODULE IncToFive ----
EXTENDS Naturals

CONSTANTS MaxValue

VARIABLES x

Init == x = 1

Next == \/ /\ x < MaxValue
             /\ x' = x + 1
         \/ /\ x = MaxValue
             /\ x' = x

Spec ==
    INIT Init
    /\ NEXT Next
    /\ WF_vars(<<x>>, Next)

Inv == \/ x \in 1..MaxValue
     \/ x = MaxValue

StutteringInv == x <= MaxValue

AlwaysAtFive == <>(x = MaxValue) /\ [](x = MaxValue)

SpecWithProperties ==
    Spec /\ Inv /\ StutteringInv /\ AlwaysAtFive

====