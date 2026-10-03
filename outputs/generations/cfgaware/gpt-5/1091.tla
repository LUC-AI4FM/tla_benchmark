----------------------------- MODULE PCR -----------------------------
EXTENDS Naturals, Integers

(*
A very abstract PCR cycle:
- Heating and cooling only affect the temperature/phase.
- Annealing nondeterministically consumes some number of available primers and
  single-stranded templates to form template-primer hybrids.
- Extension converts some number of hybrids into double-stranded DNA.
Basic safety properties (typing, nonnegativity, and a count-preservation invariant)
are provided. A liveness claim such as eventual primer depletion can be added,
but generally does not hold in this coarse model.
*)

VARIABLES temp, phase, primers, dsDNA, ssTemplates, hybrids, initialTotal

Temps  == {"Hot", "Cool"}
Phases == {"Heat", "CoolDown", "Anneal", "Extend"}

Min(a, b) == IF a <= b THEN a ELSE b

Total == ssTemplates + hybrids + dsDNA

Init ==
  /\ temp = "Cool"
  /\ phase = "Heat"
  /\ primers \in Nat
  /\ dsDNA \in Nat
  /\ ssTemplates \in Nat
  /\ hybrids \in Nat
  /\ initialTotal = Total

HeatAction ==
  /\ phase = "Heat"
  /\ temp' = "Hot"
  /\ phase' = "CoolDown"
  /\ UNCHANGED <<primers, dsDNA, ssTemplates, hybrids, initialTotal>>

CoolAction ==
  /\ phase = "CoolDown"
  /\ temp' = "Cool"
  /\ phase' = "Anneal"
  /\ UNCHANGED <<primers, dsDNA, ssTemplates, hybrids, initialTotal>>

AnnealAction ==
  /\ phase = "Anneal"
  /\ temp = "Cool"
  /\ \E k \in 0..Min(primers, ssTemplates):
       /\ primers'     = primers - k
       /\ ssTemplates' = ssTemplates - k
       /\ hybrids'     = hybrids + k
       /\ phase'       = "Extend"
       /\ UNCHANGED <<dsDNA, temp, initialTotal>>

ExtendAction ==
  /\ phase = "Extend"
  /\ \E m \in 0..hybrids:
       /\ hybrids' = hybrids - m
       /\ dsDNA'   = dsDNA + m
       /\ phase'   = "Heat"
       /\ UNCHANGED <<primers, ssTemplates, temp, initialTotal>>

Next == HeatAction \/ CoolAction \/ AnnealAction \/ ExtendAction

vars == <<temp, phase, primers, dsDNA, ssTemplates, hybrids, initialTotal>>

Spec == Init /\ [][Next]_vars

(*
Safety-style properties
*)
TypeOK ==
  /\ temp \in Temps
  /\ phase \in Phases
  /\ primers \in Nat
  /\ dsDNA \in Nat
  /\ ssTemplates \in Nat
  /\ hybrids \in Nat
  /\ initialTotal \in Nat

primerPositive == primers >= 0

preservationInvariant == Total = initialTotal

preservationProperty == [] preservationInvariant
======================================================================