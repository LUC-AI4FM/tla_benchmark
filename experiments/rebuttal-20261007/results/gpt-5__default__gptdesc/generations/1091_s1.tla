------------------------------- MODULE PCR -------------------------------

EXTENDS Naturals

CONSTANT TOTAL

VARIABLES Temperature, Phase, P, D, T, H

(*
  Helper operators
*)
Min(a, b) == IF a <= b THEN a ELSE b

Vars == << Temperature, Phase, P, D, T, H >>

(*
  State invariants (safety-style)
*)
TypeOK ==
  /\ Temperature \in {"High", "Low"}
  /\ Phase \in {"Heating", "Cooling", "Annealing", "Extension"}
  /\ P \in Nat
  /\ D \in Nat
  /\ T \in Nat
  /\ H \in Nat
  /\ TOTAL \in Nat

NonNeg ==
  /\ P >= 0
  /\ D >= 0
  /\ T >= 0
  /\ H >= 0

CountPreserved ==
  T + H + D = TOTAL

(*
  Initial states
*)
Init ==
  /\ Phase = "Heating"
  /\ Temperature \in {"High", "Low"}
  /\ P \in Nat
  /\ D \in Nat
  /\ T \in Nat
  /\ H \in Nat
  /\ T + H + D = TOTAL

(*
  Actions
*)
HeatingAct ==
  /\ Phase = "Heating"
  /\ Temperature' = "High"
  /\ UNCHANGED << P, D, T, H >>
  /\ Phase' = "Cooling"

CoolingAct ==
  /\ Phase = "Cooling"
  /\ Temperature' = "Low"
  /\ UNCHANGED << P, D, T, H >>
  /\ Phase' = "Annealing"

AnnealAct ==
  /\ Phase = "Annealing"
  /\ Temperature = "Low"
  /\ \E k \in { kk \in Nat : kk <= Min(P, T) }:
       /\ P' = P - k
       /\ T' = T - k
       /\ H' = H + k
       /\ D' = D
  /\ Temperature' = Temperature
  /\ Phase' = "Extension"

ExtendAct ==
  /\ Phase = "Extension"
  /\ \E e \in { ee \in Nat : ee <= H }:
       /\ H' = H - e
       /\ D' = D + e
       /\ P' = P
       /\ T' = T
  /\ Temperature' = Temperature
  /\ Phase' = "Heating"

Next ==
  HeatingAct \/ CoolingAct \/ AnnealAct \/ ExtendAct

(*
  Temporal specification with progress fairness on phase actions
  to rule out arbitrary stuttering, but no fairness on the amount
  consumed/converted within Anneal/Extend.
*)
Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ WF_Vars(HeatingAct)
  /\ WF_Vars(CoolingAct)
  /\ WF_Vars(AnnealAct)
  /\ WF_Vars(ExtendAct)

(*
  Liveness property (does not hold in general for this abstraction):
  eventual primer depletion.
*)
EventuallyPrimerDepletion ==
  <> (P = 0)

(*
  Safety theorems
*)
THEOREM Spec => []TypeOK
THEOREM Spec => []NonNeg
THEOREM Spec => []CountPreserved

============================================================================