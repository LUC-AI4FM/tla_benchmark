---------------------------- MODULE PCR ----------------------------
EXTENDS Naturals, TLC

(*
A very abstract model of the PCR cycle.
State includes:
- temp: temperature mode
- phase: control mode cycling through actions
- primers: count of free primers
- ds: count of double-stranded DNA molecules
- ss: count of single-stranded template strands
- hyb: count of template-primer hybrids

Actions alternate in the order: Heating -> Cooling -> Annealing -> Extension.
Annealing nondeterministically consumes available primers and templates to form hybrids.
Extension nondeterministically converts hybrids into double-stranded DNA, consuming an equal
number of single-stranded templates so that the abstract "strand mass" ss + hyb + 2*ds is preserved.

Safety-style properties:
- typing/nonnegativity (TypeOK)
- count preservation (CountPreserved): ss + hyb + 2*ds = TotalMass0

Liveness property (does not hold in this coarse model):
- PrimersDeplete: <> (primers = 0)
*)

CONSTANTS
  Primers0,    \* Initial number of free primers
  DNA0,        \* Initial number of double-stranded DNA molecules
  Templates0,  \* Initial number of single-stranded templates
  Hybrids0,    \* Initial number of template-primer hybrids
  InitTemp,    \* Initial temperature
  StartPhase   \* Initial control phase

Temps  == {"Hot", "Cool"}
Phases == {"Heating", "Cooling", "Annealing", "Extension"}

ASSUME
  /\ Primers0 \in Nat
  /\ DNA0 \in Nat
  /\ Templates0 \in Nat
  /\ Hybrids0 \in Nat
  /\ InitTemp \in Temps
  /\ StartPhase \in Phases

VARIABLES temp, primers, ds, ss, hyb, phase

vars == << temp, primers, ds, ss, hyb, phase >>

TotalMass0 == Templates0 + Hybrids0 + 2 * DNA0

TypeOK ==
  /\ temp \in Temps
  /\ phase \in Phases
  /\ primers \in Nat
  /\ ds \in Nat
  /\ ss \in Nat
  /\ hyb \in Nat

CountPreserved ==
  ss + hyb + 2 * ds = TotalMass0

Init ==
  /\ temp = InitTemp
  /\ phase = StartPhase
  /\ primers = Primers0
  /\ ds = DNA0
  /\ ss = Templates0
  /\ hyb = Hybrids0
  /\ TypeOK
  /\ CountPreserved

Min(a, b) == IF a <= b THEN a ELSE b

Heating ==
  /\ phase = "Heating"
  /\ temp' = "Hot"
  /\ ss' = ss + 2 * ds
  /\ ds' = 0
  /\ hyb' = hyb
  /\ primers' = primers
  /\ phase' = "Cooling"

Cooling ==
  /\ phase = "Cooling"
  /\ temp' = "Cool"
  /\ UNCHANGED << primers, ds, ss, hyb >>
  /\ phase' = "Annealing"

Anneal ==
  /\ phase = "Annealing"
  /\ temp = "Cool"
  /\ \E a \in 0..Min(primers, ss):
        /\ primers' = primers - a
        /\ ss' = ss - a
        /\ hyb' = hyb + a
        /\ ds' = ds
        /\ temp' = temp
        /\ phase' = "Extension"

Extend ==
  /\ phase = "Extension"
  /\ temp = "Hot"
  /\ \E e \in 0..Min(hyb, ss):
        /\ ds' = ds + e
        /\ hyb' = hyb - e
        /\ ss' = ss - e
        /\ primers' = primers
        /\ temp' = temp
        /\ phase' = "Heating"

Next == Heating \/ Cooling \/ Anneal \/ Extend

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Heating)
  /\ WF_vars(Cooling)
  /\ WF_vars(Anneal)
  /\ WF_vars(Extend)

SafetyInvariants ==
  /\ TypeOK
  /\ CountPreserved

(*
Liveness property claiming eventual primer depletion.
Note: This property does not hold in this abstract model because Anneal and Extend
may repeatedly choose to consume zero items.
*)
PrimersDeplete == <> (primers = 0)

============================================================================