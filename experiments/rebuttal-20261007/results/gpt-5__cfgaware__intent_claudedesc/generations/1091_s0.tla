----------------------------- MODULE PCR -----------------------------
EXTENDS Naturals

CONSTANTS InitDS, InitPrimers

VARIABLES ds, tmpl, pr, hyb, phase

Phases == {"High", "Cool", "Warm", "Medium"}

vars == << ds, tmpl, pr, hyb, phase >>

Min(a, b) == IF a < b THEN a ELSE b

Init ==
  /\ ds = InitDS
  /\ tmpl = 0
  /\ pr = InitPrimers
  /\ hyb = 0
  /\ phase = "Cool"

Denature ==
  /\ phase = "High"
  /\ ds' = 0
  /\ hyb' = 0
  /\ tmpl' = tmpl + (2 * ds) + hyb
  /\ pr' = pr + hyb
  /\ phase' = "Cool"

CoolToWarm ==
  /\ phase = "Cool"
  /\ UNCHANGED << ds, tmpl, pr, hyb >>
  /\ phase' = "Warm"

Anneal ==
  /\ phase = "Warm"
  /\ \E a \in 0..Min(tmpl, pr):
       /\ ds' = ds
       /\ tmpl' = tmpl - a
       /\ pr' = pr - a
       /\ hyb' = hyb + a
       /\ phase' = "Medium"

Extend ==
  /\ phase = "Medium"
  /\ ds' = ds + hyb
  /\ hyb' = 0
  /\ UNCHANGED << tmpl, pr >>
  /\ phase' = "High"

Next == Denature \/ CoolToWarm \/ Anneal \/ Extend

TypeOK ==
  /\ ds \in Nat
  /\ tmpl \in Nat
  /\ pr \in Nat
  /\ hyb \in Nat
  /\ phase \in Phases

Total == pr + tmpl + (2 * ds) + (2 * hyb)

ConstTotal == InitPrimers + (2 * InitDS)

preservationInvariant == Total = ConstTotal

preservationProperty == [] (Total = ConstTotal)

primerPositive == InitPrimers > 0

Spec == Init /\ [][Next]_vars
=====================================================================