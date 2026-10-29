--------------------------- MODULE MC_Session11afair ---------------------------
(***************************************************************************)
(* Model-checking configuration for the fair alternating bit protocol      *)
(* specification (high-level ABSpec as in Session11afair).  The parent     *)
(* module's definitions are reproduced here so that this module is          *)
(* self-contained.                                                          *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS Data

(* Model value instantiation for the constant Data. *)
const_Data == {"Fred", "Mary", "Ted"}

ASSUME Data = const_Data

VARIABLES AVar, BVar

vars == <<AVar, BVar>>

(***************************************************************************)
(* A message is a pair consisting of a data item and a sequence bit.       *)
(***************************************************************************)
Messages == Data \X {0, 1}

ABSpec_TypeOK == /\ AVar \in Messages
                 /\ BVar \in Messages

-----------------------------------------------------------------------------
Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar

(* A sends a new value once B has received the previous one. *)
A == /\ AVar = BVar
     /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
     /\ UNCHANGED BVar

(* B receives the value that A has sent. *)
B == /\ AVar # BVar
     /\ BVar' = AVar
     /\ UNCHANGED AVar

Next == A \/ B

Spec == Init /\ [][Next]_vars

(* Fair specification: weak fairness on the next-state action. *)
FairSpec == Spec /\ WF_vars(Next)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
ABSpec_Inv == (AVar[2] = BVar[2]) => (AVar = BVar)

(***************************************************************************)
(* Temporal properties                                                     *)
(***************************************************************************)
InfinitelyAlternating == /\ []<>(AVar = BVar)
                         /\ []<>(AVar # BVar)

Liveness == (AVar # BVar) ~> (AVar = BVar)

-----------------------------------------------------------------------------
THEOREM FairSpec => [](ABSpec_TypeOK /\ ABSpec_Inv)
THEOREM FairSpec => InfinitelyAlternating /\ Liveness
=============================================================================