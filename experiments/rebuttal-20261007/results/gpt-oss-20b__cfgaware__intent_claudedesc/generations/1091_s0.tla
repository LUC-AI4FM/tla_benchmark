------------------------------ MODULE PCR ------------------------------
EXTENDS Naturals, TLC

CONSTANTS initDNA, initPrimers

VARIABLES dna, templates, primers, hybrids, temp

TempSet == {"High", "Cooling", "Warm", "Medium"}

TypeOK ==
  /\ dna \in Nat
  /\ templates \in Nat
  /\ primers \in Nat
  /\ hybrids \in Nat
  /\ temp \in TempSet

primerPositive == primers > 0

preservationInvariant ==
  primers + templates + 2*dna + 2*hybrids = initPrimers + 2*initDNA

preservationProperty == [] preservationInvariant

vars == <<dna, templates, primers, hybrids, temp>>

Init ==
  TypeOK
  /\ dna = initDNA
  /\ primers = initPrimers
  /\ templates = 0
  /\ hybrids = 0
  /\ temp = "Medium"

Min(a,b) == IF a <= b THEN a ELSE b

HighStep ==
  /\ temp = "High"
  /\ dna'   = 0
  /\ hybrids'= 0
  /\ templates'= dna + hybrids
  /\ primers' = primers + hybrids
  /\ temp'    = "Cooling"

CoolingStep ==
  /\ temp = "Cooling"
  /\ temp' = "Warm"

WarmStep ==
  /\ temp = "Warm"
  /\ \E k \in 0..Min(primers, templates) :
        dna'      = dna
     /\ hybrids'  = hybrids + k
     /\ primers'  = primers - k
     /\ templates'= templates - k
     /\ temp'     = "Medium"

MediumStep ==
  /\ temp = "Medium"
  /\ dna'      = dna + hybrids
  /\ templates'= templates - hybrids
  /\ hybrids'  = 0
  /\ temp'     = "High"

Next == HighStep \/ CoolingStep \/ WarmStep \/ MediumStep

Spec == Init /\ [][Next]_vars
=============================================================================