----------------------------- MODULE PCR -----------------------------
EXTENDS Naturals

CONSTANTS
  DS0, \* initial double-stranded molecules
  SS0, \* initial single-stranded templates
  P0,  \* initial free primers (pooled)
  H0,  \* initial primer–template hybrids
  StartTemp \* initial temperature phase

(*
  Phases of the thermocycler
*)
Denat  == "Denaturation"
Anneal == "Annealing"
Extend == "Extension"
Phases == {Denat, Anneal, Extend}

NextPhase(t) ==
  IF t = Denat THEN Anneal
  ELSE IF t = Anneal THEN Extend
  ELSE Denat

(*
  State variables
*)
VARIABLES ds, ss, P, h, temp

vars == << ds, ss, P, h, temp >>

(*
  Helpers
*)
Min2(a, b) == IF a < b THEN a ELSE b

Total == 2*ds + ss + P + 2*h
CONS0 == 2*DS0 + SS0 + P0 + 2*H0

(*
  State typing and basic safety conditions
*)
TypeOK ==
  /\ ds \in Nat
  /\ ss \in Nat
  /\ P  \in Nat
  /\ h  \in Nat
  /\ temp \in Phases

(*
  Positive-primer assumption/predicate (useful for scenarios with available primers)
*)
primerPositive == P0 > 0

(*
  Mass-preservation (linear invariant over nucleotide-containing species)
*)
preservationInvariant == Total = CONS0

(*
  Safety property: nonnegativity and preservation hold in all reachable states
*)
preservationProperty == [](TypeOK /\ preservationInvariant)

(*
  Initial state
*)
Init ==
  /\ ds = DS0
  /\ ss = SS0
  /\ P  = P0
  /\ h  = H0
  /\ StartTemp \in Phases
  /\ temp = StartTemp
  /\ TypeOK
  /\ preservationInvariant

(*
  Phase-specific reaction steps
*)
DenatureStep ==
  /\ temp = Denat
  /\ ds' = 0
  /\ h'  = 0
  /\ ss' = ss + 2*ds + h
  /\ P'  = P + h
  /\ temp' = temp

AnnealStep ==
  /\ temp = Anneal
  /\ \E a \in 0..Min2(P, ss):
       /\ P'  = P - a
       /\ ss' = ss - a
       /\ h'  = h + a
       /\ ds' = ds
       /\ temp' = temp

ExtendStep ==
  /\ temp = Extend
  /\ \E e \in 0..h:
       /\ ds' = ds + e
       /\ h'  = h - e
       /\ P'  = P
       /\ ss' = ss
       /\ temp' = temp

(*
  Temperature advancement (thermocycler progression)
*)
AdvanceTemp ==
  /\ temp' = NextPhase(temp)
  /\ UNCHANGED << ds, ss, P, h >>

Next ==
  DenatureStep \/ AnnealStep \/ ExtendStep \/ AdvanceTemp

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(AdvanceTemp)
======================================================================