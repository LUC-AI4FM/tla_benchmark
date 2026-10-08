MODULE PCRCycle
EXTENDS Naturals, Integers

CONSTANTS PRIMERS0, TEMPLATES0, TEMP_HIGH, TEMP_LOW

VARIABLES temp, prim, tmpl, hyb, dna

Init ==
  /\ temp = TEMP_LOW
  /\ prim = PRIMERS0
  /\ tmpl = TEMPLATES0
  /\ hyb = 0
  /\ dna = 0

Heating ==
  /\ temp' = TEMP_HIGH
  /\ prim' = prim
  /\ tmpl' = tmpl
  /\ hyb' = hyb
  /\ dna' = dna

Cooling ==
  /\ temp' = TEMP_LOW
  /\ prim' = prim
  /\ tmpl' = tmpl
  /\ hyb' = hyb
  /\ dna' = dna

Annealing ==
  \E k \in Nat :
    /\ k <= prim
    /\ k <= tmpl
    /\ prim' = prim - k
    /\ tmpl' = tmpl - k
    /\ hyb' = hyb + k
    /\ dna' = dna
    /\ temp' = temp

Extension ==
  \E k \in Nat :
    /\ k <= hyb
    /\ hyb' = hyb - k
    /\ dna' = dna + k
    /\ prim' = prim
    /\ tmpl' = tmpl
    /\ temp' = temp

Next == Heating \/ Cooling \/ Annealing \/ Extension

TypeInvariant ==
  /\ temp \in Int
  /\ prim \in Nat
  /\ tmpl \in Nat
  /\ hyb \in Nat
  /\ dna \in Nat

NonNegativity ==
  /\ prim >= 0
  /\ tmpl >= 0
  /\ hyb >= 0
  /\ dna >= 0

TotalCount ==
  LET total0 == PRIMERS0 + TEMPLATES0 IN
  prim + tmpl + hyb + dna = total0

SafetyInv == TypeInvariant /\ NonNegativity /\ TotalCount

PrimersDepleted == <> (prim = 0)

Spec == Init /\ [][Next]_<<temp, prim, tmpl, hyb, dna>> /\ SafetyInv /\ PrimersDepleted

END MODULE