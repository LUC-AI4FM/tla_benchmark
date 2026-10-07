----------------------------- MODULE PCR -----------------------------
EXTENDS Naturals, TLC

CONSTANTS P0, D0, T0, H0

ASSUME /\ P0 \in Nat
       /\ D0 \in Nat
       /\ T0 \in Nat
       /\ H0 \in Nat

VARIABLES phase, temp, P, D, T, H

SetPhases == {"Heat", "Cool", "Anneal", "Extend"}
SetTemps  == {"High", "Low"}

Min2(a, b) == IF a <= b THEN a ELSE b

vars == << phase, temp, P, D, T, H >>

Init ==
  /\ phase = "Heat"
  /\ temp  = "High"
  /\ P = P0
  /\ D = D0
  /\ T = T0
  /\ H = H0

Heat ==
  /\ phase = "Heat"
  /\ \E d \in 0..D:
       /\ D' = D - d
       /\ T' = T + 2 * d
       /\ temp' = "High"
       /\ phase' = "Cool"
       /\ UNCHANGED << P, H >>

Cool ==
  /\ phase = "Cool"
  /\ temp' = "Low"
  /\ phase' = "Anneal"
  /\ UNCHANGED << P, D, T, H >>

Anneal ==
  /\ phase = "Anneal"
  /\ temp = "Low"
  /\ \E k \in 0..Min2(P, T):
       /\ P' = P - k
       /\ T' = T - k
       /\ H' = H + k
       /\ D' = D
       /\ temp' = temp
       /\ phase' = "Extend"

Extend ==
  /\ phase = "Extend"
  /\ \E m \in 0..H:
       /\ H' = H - m
       /\ D' = D + m
       /\ P' = P
       /\ T' = T
       /\ temp' = "High"
       /\ phase' = "Heat"

Next == Heat \/ Cool \/ Anneal \/ Extend

Spec == Init /\ [][Next]_vars

(*
  Safety-style invariants
*)
TypeOK ==
  /\ phase \in SetPhases
  /\ temp  \in SetTemps
  /\ P \in Nat
  /\ D \in Nat
  /\ T \in Nat
  /\ H \in Nat

NonNeg ==
  /\ P >= 0
  /\ D >= 0
  /\ T >= 0
  /\ H >= 0

CountPreserved ==
  2 * D + T + 2 * H + P = 2 * D0 + T0 + 2 * H0 + P0

(*
  Liveness property (intentionally false in general):
  Eventually, primers are depleted.
*)
PrimerDepletion == <> (P = 0)
======================================================================