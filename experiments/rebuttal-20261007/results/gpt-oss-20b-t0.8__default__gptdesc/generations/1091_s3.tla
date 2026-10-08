MODULE PCR
EXTENDS Naturals, TLC

CONSTANTS HeatingTemp, CoolingTemp, AnnealingTemp, ExtensionTemp,
          InitPrimers, InitTemplates

VARIABLES temp, primers, templates, hybrids, dna

vars == <<temp, primers, templates, hybrids, dna>>

(* Typing and nonnegativity *)
Typs ==
    0 <= primers /\ 0 <= templates /\ 0 <= hybrids /\ 0 <= dna

InitTotal == InitPrimers + InitTemplates

Init ==
    temp = CoolingTemp /\
    primers = InitPrimers /\
    templates = InitTemplates /\
    hybrids = 0 /\
    dna = 0 /\
    Typs

Heating ==
    temp' = HeatingTemp /\ UNCHANGED <<primers, templates, hybrids, dna>>

Cooling ==
    temp' = CoolingTemp /\ UNCHANGED <<primers, templates, hybrids, dna>>

Annealing ==
    /\ temp' = AnnealingTemp
    /\ \E k1, k2 \in Nat :
           0 <= k1 /\ k1 <= primers /\
           0 <= k2 /\ k2 <= templates /\
           primers' = primers - k1 /\
           templates' = templates - k2 /\
           hybrids' = hybrids + k1 + k2 /\
           dna' = dna

Extension ==
    /\ temp' = ExtensionTemp
    /\ \E h \in Nat :
           0 <= h /\ h <= hybrids /\
           hybrids' = hybrids - h /\
           dna' = dna + h /\
           primers' = primers /\
           templates' = templates

Next == Heating \/ Cooling \/ Annealing \/ Extension

PreserveCount ==
    (primers + templates + hybrids + dna) =
    (primers' + templates' + hybrids' + dna')

Spec == Init /\ [][Next]_vars /\ Typs /\ PreserveCount

Liveness == <> (primers = 0)