---------------------------- MODULE MC_Session11a ----------------------------
EXTENDS Naturals

CONSTANT Data

VARIABLES AVar, BVar

vars == <<AVar, BVar>>

ConstData == {"Fred", "Mary", "Ted"}

Msgs == Data \X {0, 1}

-----------------------------------------------------------------------------
(* Alternating bit specification (sender A, receiver B)                     *)

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar

A == /\ AVar = BVar
     /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
     /\ UNCHANGED BVar

B == /\ AVar # BVar
     /\ BVar' = AVar
     /\ UNCHANGED AVar

Next == A \/ B

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants checked by the model                                          *)

ABSpec_TypeOK == /\ AVar \in Msgs
                 /\ BVar \in Msgs

ABSpec_Inv == (AVar[2] = BVar[2]) => (AVar = BVar)

=============================================================================