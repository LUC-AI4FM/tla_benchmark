---------------------------- MODULE PCRCycle ----------------------------
EXTENDS Naturals

CONSTANTS InitPrimers, InitDNA, MaxTemp, MinTemp

VARIABLES temp, primers, dsDNA, ssDNA, hybrids, phase

vars == <<temp, primers, dsDNA, ssDNA, hybrids, phase>>

Phases == {"heating", "cooling", "annealing", "extension"}

TypeOK ==
    /\ temp \in Nat
    /\ primers \in Nat
    /\ dsDNA \in Nat
    /\ ssDNA \in Nat
    /\ hybrids \in Nat
    /\ phase \in Phases

Init ==
    /\ temp = MinTemp
    /\ primers = InitPrimers
    /\ dsDNA = InitDNA
    /\ ssDNA = 0
    /\ hybrids = 0
    /\ phase = "heating"

Heat ==
    /\ phase = "heating"
    /\ temp' = MaxTemp
    /\ ssDNA' = ssDNA + (2 * dsDNA)
    /\ dsDNA' = 0
    /\ primers' = primers
    /\ hybrids' = hybrids
    /\ phase' = "cooling"

Cool ==
    /\ phase = "cooling"
    /\ temp' = MinTemp
    /\ primers' = primers
    /\ dsDNA' = dsDNA
    /\ ssDNA' = ssDNA
    /\ hybrids' = hybrids
    /\ phase' = "annealing"

Anneal ==
    /\ phase = "annealing"
    /\ \E n \in 0..primers :
        /\ n <= ssDNA
        /\ primers' = primers - n
        /\ ssDNA' = ssDNA - n
        /\ hybrids' = hybrids + n
        /\ dsDNA' = dsDNA
        /\ temp' = temp
        /\ phase' = "extension"

Extend ==
    /\ phase = "extension"
    /\ dsDNA' = dsDNA + hybrids
    /\ hybrids' = 0
    /\ primers' = primers
    /\ ssDNA' = ssDNA
    /\ temp' = temp
    /\ phase' = "heating"

Next == Heat \/ Cool \/ Anneal \/ Extend

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

NonNegativity ==
    /\ primers >= 0
    /\ dsDNA >= 0
    /\ ssDNA >= 0
    /\ hybrids >= 0

CountPreservation ==
    (2 * dsDNA) + ssDNA + hybrids + primers = (2 * InitDNA) + InitPrimers

SafetyInvariant ==
    /\ TypeOK
    /\ NonNegativity
    /\ CountPreservation

PrimerDepletion == <>(primers = 0)

=========================================================================