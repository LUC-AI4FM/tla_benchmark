---------------------------- MODULE MC_Session11a ----------------------------
(***************************************************************************)
(* Model-checking configuration for the alternating bit high-level spec    *)
(* (ABSpec, from Session11a).  The ABSpec definitions are reproduced here  *)
(* so that the module is self-contained and parses on its own.             *)
(***************************************************************************)
EXTENDS Naturals, TLC

CONSTANT Data

VARIABLES AVar, BVar

vars == <<AVar, BVar>>

(***************************************************************************)
(* Concrete instantiation of the constant Data used for model checking.    *)
(***************************************************************************)
const_Data == {"Fred", "Mary", "Ted"}

ASSUME Data = const_Data

(***************************************************************************)
(* A message is a pair of a data value and a bit.                          *)
(***************************************************************************)
Msgs == Data \X {0, 1}

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar

(***************************************************************************)
(* A sends a new value with the complemented bit once B has caught up.     *)
(***************************************************************************)
A == /\ AVar = BVar
     /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
     /\ BVar' = BVar

(***************************************************************************)
(* B receives the value currently held by A.                               *)
(***************************************************************************)
B == /\ AVar # BVar
     /\ BVar' = AVar
     /\ AVar' = AVar

Next == A \/ B

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* Invariants checked by the model.                                        *)
(***************************************************************************)
ABSpec_TypeOK == /\ AVar \in Msgs
                 /\ BVar \in Msgs

ABSpec_Inv == (AVar[2] = BVar[2]) => (AVar = BVar)

(***************************************************************************)
(* Liveness (under FairSpec): every value sent by A is eventually          *)
(* received by B.                                                          *)
(***************************************************************************)
Liveness == \A v \in Data \X {0, 1} : (AVar = v) ~> (BVar = v)

THEOREM Spec => [](ABSpec_TypeOK /\ ABSpec_Inv)
THEOREM FairSpec => Liveness
=============================================================================