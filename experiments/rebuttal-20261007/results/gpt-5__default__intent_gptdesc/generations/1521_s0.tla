----------------------------- MODULE CoffeeCan -----------------------------

EXTENDS Naturals, Integers

CONSTANTS Useless

VARIABLES B, W, P

vars == <<B, W, P>>

Tot == B + W
CanStep == Tot >= 2
Terminated == Tot < 2

Init ==
  /\ B \in Nat
  /\ W \in Nat
  /\ Tot >= 1
  /\ P = (W \mod 2)

TwoBlack ==
  /\ B >= 2
  /\ B' = B - 1
  /\ W' = W
  /\ P' = P

BlackWhite ==
  /\ B >= 1
  /\ W >= 1
  /\ B' = B - 1
  /\ W' = W
  /\ P' = P

TwoWhite ==
  /\ W >= 2
  /\ B' = B + 1
  /\ W' = W - 2
  /\ P' = P

Next ==
  /\ CanStep
  /\ (TwoBlack \/ BlackWhite \/ TwoWhite)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

(*
 Safety and invariants
*)

TypeOK ==
  B \in Nat /\ W \in Nat /\ P \in {0, 1}

SafetyDecrease ==
  [](Next => Tot' = Tot - 1)

EnabledEquiv ==
  [](ENABLED Next <=> CanStep)

ParityStep ==
  [](Next => (W' \mod 2) = (W \mod 2))

ParityInv ==
  [](W \mod 2 = P)

(*
 Liveness / termination and final-state characterization
*)

Termination ==
  <>(Tot = 1)

FinalState ==
  /\ Tot = 1
  /\ IF P = 0
     THEN /\ B = 1 /\ W = 0
     ELSE /\ B = 0 /\ W = 1

FinalStateEventually ==
  <>FinalState

THEOREM Spec => []TypeOK
THEOREM Spec => SafetyDecrease
THEOREM Spec => EnabledEquiv
THEOREM Spec => ParityStep
THEOREM Spec => ParityInv
THEOREM Spec => Termination
THEOREM Spec => FinalStateEventually

==============================