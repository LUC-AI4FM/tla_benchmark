------------------------------ MODULE PCR ------------------------------

EXTENDS Naturals

CONSTANTS DNA0, Primer0

ASSUME DNA0 \in Nat /\ Primer0 \in Nat

VARIABLES ds, tmpl, prim, hyb, t

Temps == {"High", "Cool", "Warm", "Medium"}

Init ==
  /\ ds   = DNA0
  /\ prim = Primer0
  /\ tmpl = 0
  /\ hyb  = 0
  /\ t    = "Medium"

Denature ==
  /\ t = "High"
  /\ ds'   = 0
  /\ hyb'  = 0
  /\ tmpl' = tmpl + (2 * ds) + hyb
  /\ prim' = prim + hyb
  /\ t'    = "Cool"

CoolToWarm ==
  /\ t = "Cool"
  /\ ds'   = ds
  /\ tmpl' = tmpl
  /\ prim' = prim
  /\ hyb'  = hyb
  /\ t'    = "Warm"

Anneal ==
  /\ t = "Warm"
  /\ LET maxBind == IF prim <= tmpl THEN prim ELSE tmpl IN
     \E k \in 0..maxBind:
       /\ ds'   = ds
       /\ tmpl' = tmpl - k
       /\ prim' = prim - k
       /\ hyb'  = hyb + k
       /\ t'    = "Medium"

Extend ==
  /\ t = "Medium"
  /\ ds'   = ds + hyb
  /\ tmpl' = tmpl
  /\ prim' = prim
  /\ hyb'  = 0
  /\ t'    = "High"

Next == Denature \/ CoolToWarm \/ Anneal \/ Extend

Vars == << ds, tmpl, prim, hyb, t >>

Spec == Init /\ [][Next]_Vars

TotalStrands == prim + tmpl + (2 * ds) + (2 * hyb)

InitialTotal == Primer0 + (2 * DNA0)

TypeInv ==
  /\ ds \in Nat
  /\ tmpl \in Nat
  /\ prim \in Nat
  /\ hyb \in Nat
  /\ t \in Temps

ConservationInv == TotalStrands = InitialTotal

ConservationAlways == [](TotalStrands = InitialTotal)

============================================================================