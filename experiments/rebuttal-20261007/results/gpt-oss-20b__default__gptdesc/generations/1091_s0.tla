MODULE PCR

EXTENDS Naturals, TLC

CONSTANT Total

VARIABLES temp, primers, ssTemplates, hybrids, dsDNA

vars == <<temp, primers, ssTemplates, hybrids, dsDNA>>

Init ==
  /\ temp = 0
  /\ primers + ssTemplates + hybrids + dsDNA = Total
  /\ primers >= 0 /\ ssTemplates >= 0 /\ hybrids >= 0 /\ dsDNA >= 0

Heating ==
  /\ temp' = temp + 1
  /\ UNCHANGED <<primers, ssTemplates, hybrids, dsDNA>>

Cooling ==
  /\ temp > 0
  /\ temp' = temp - 1
  /\ UNCHANGED <<primers, ssTemplates, hybrids, dsDNA>>

Annealing ==
  /\ ∃ k ∈ Nat :
       /\ k <= primers
       /\ k <= ssTemplates
       /\ temp' = temp
       /\ primers' = primers - k
       /\ ssTemplates' = ssTemplates - k
       /\ hybrids' = hybrids + k
       /\ dsDNA' = dsDNA

Extension ==
  /\ temp' = temp
  /\ primers' = primers
  /\ ssTemplates' = ssTemplates
  /\ hybrids' = 0
  /\ dsDNA' = dsDNA + hybrids

Next == Heating \/ Cooling \/ Annealing \/ Extension

TypeInv ==
  /\ temp ∈ Nat
  /\ primers ∈ Nat
  /\ ssTemplates ∈ Nat
  /\ hybrids ∈ Nat
  /\ dsDNA ∈ Nat

NonNeg ==
  /\ primers >= 0
  /\ ssTemplates >= 0
  /\ hybrids >= 0
  /\ dsDNA >= 0

CountPreservation ==
  /\ primers + ssTemplates + hybrids + dsDNA = Total

Safety == TypeInv /\ NonNeg /\ CountPreservation

Liveness == <> (primers = 0)

Spec == Init /\ [][Next]_vars /\ Safety /\ Liveness

END MODULE