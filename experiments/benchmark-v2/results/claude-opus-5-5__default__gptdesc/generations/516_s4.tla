------------------------------- MODULE ABSpec -------------------------------
(***************************************************************************)
(* Abstract specification of the Alternating Bit protocol.                 *)
(*                                                                         *)
(* It describes what the protocol is supposed to accomplish: process A     *)
(* repeatedly chooses a new data value and flips the bit when the bits of  *)
(* AVar and BVar match.  Process B copies A's value when they differ.      *)
(***************************************************************************)
EXTENDS Integers

CONSTANT Data   \* The set of data values that can be sent.

(***************************************************************************
--algorithm ABSpec {
  variables AVar \in Data \X {1}, BVar = AVar ;

  fair process (A = "A") {
    a: while (TRUE) {
         await AVar = BVar ;
         with (d \in Data) { AVar := <<d, 1 - AVar[2]>> }
       }
  }

  fair process (B = "B") {
    b: while (TRUE) {
         await AVar # BVar ;
         BVar := AVar
       }
  }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES AVar, BVar

vars == << AVar, BVar >>

ProcSet == {"A"} \cup {"B"}

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar

A == /\ AVar = BVar
     /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
     /\ BVar' = BVar

B == /\ AVar # BVar
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
(* Safety properties.                                                      *)
(***************************************************************************)
Messages == Data \X {0, 1}

TypeOK == /\ AVar \in Messages
          /\ BVar \in Messages

\* Whenever the bits agree, the whole messages agree (B has received A's value).
Inv == (AVar[2] = BVar[2]) => (AVar = BVar)

(***************************************************************************)
(* Liveness property: every value chosen by A is eventually received by B.*)
(***************************************************************************)
FairSpec == Spec

Liveness == \A v \in Messages : (AVar = v) ~> (BVar = v)

THEOREM Spec => [](TypeOK /\ Inv)
THEOREM Spec => Liveness
=============================================================================