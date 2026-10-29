------------------------------- MODULE ABSpec -------------------------------
EXTENDS Integers

CONSTANT Data

Msgs == [data : Data, bit : {0, 1}]

(***************************************************************************
--algorithm ABSpec {
  variables AVar \in Msgs, BVar = AVar ;

  fair process (A = "A") {
    a: while (TRUE) {
         await AVar.bit = BVar.bit ;
         with (d \in Data) { AVar := [data |-> d, bit |-> 1 - AVar.bit] }
       }
  }

  fair process (B = "B") {
    b: while (TRUE) {
         await AVar.bit # BVar.bit ;
         BVar := AVar
       }
  }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES AVar, BVar

vars == << AVar, BVar >>

ProcSet == {"A"} \cup {"B"}

Init == /\ AVar \in Msgs
        /\ BVar = AVar

A == /\ AVar.bit = BVar.bit
     /\ \E d \in Data :
          AVar' = [data |-> d, bit |-> 1 - AVar.bit]
     /\ BVar' = BVar

B == /\ AVar.bit # BVar.bit
     /\ BVar' = AVar
     /\ AVar' = AVar

Next == A \/ B

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(A)
        /\ WF_vars(B)
\* END TRANSLATION

TypeOK == /\ AVar \in Msgs
          /\ BVar \in Msgs

=============================================================================