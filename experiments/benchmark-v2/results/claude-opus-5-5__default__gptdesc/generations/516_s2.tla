------------------------------- MODULE ABSpec -------------------------------
(***************************************************************************)
(* Abstract specification of the Alternating Bit protocol.                 *)
(* Process A chooses a new data value and flips the bit when the bits of   *)
(* AVar and BVar match.  Process B copies AVar into BVar when the bits     *)
(* differ.  Both processes are weakly fair.                                *)
(***************************************************************************)
EXTENDS Integers

CONSTANT Data

ASSUME Data # {}

Msgs == [val : Data, bit : {0, 1}]

(***************************************************************************
--fair algorithm ABSpec {
  variables AVar \in [val : Data, bit : {1}], BVar = AVar ;

  fair process (A = "A") {
    a: while (TRUE) {
         await AVar.bit = BVar.bit ;
         with (d \in Data) { AVar := [val |-> d, bit |-> 1 - AVar.bit] }
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

Init == /\ AVar \in [val : Data, bit : {1}]
        /\ BVar = AVar

A == /\ AVar.bit = BVar.bit
     /\ \E d \in Data :
          AVar' = [val |-> d, bit |-> 1 - AVar.bit]
     /\ BVar' = BVar

B == /\ AVar.bit # BVar.bit
     /\ BVar' = AVar
     /\ AVar' = AVar

Next == A \/ B

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(A)
        /\ WF_vars(B)
\* END TRANSLATION

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
TypeOK == /\ AVar \in Msgs
          /\ BVar \in Msgs

\* Whenever the bits agree, B holds exactly the value A sent.
Inv == (AVar.bit = BVar.bit) => (AVar = BVar)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)
\* Every message chosen by A is eventually delivered to B.
Delivery == \A v \in Data, b \in {0, 1} :
              (AVar = [val |-> v, bit |-> b]) ~> (BVar = [val |-> v, bit |-> b])

\* The protocol makes progress forever: A keeps sending new messages.
Progress == \A b \in {0, 1} : []<>(AVar.bit = b)

THEOREM Spec => [](TypeOK /\ Inv)
THEOREM Spec => Delivery /\ Progress
=============================================================================