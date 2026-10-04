---------------------------- MODULE PCR ----------------------------
EXTENDS Naturals

CONSTANTS InitialDNA, InitialPrimers

VARIABLES dsDNA, templates, primers, hybrids, temp

vars == <<dsDNA, templates, primers, hybrids, temp>>

TypeOK ==
    /\ dsDNA \in Nat
    /\ templates \in Nat
    /\ primers \in Nat
    /\ hybrids \in Nat
    /\ temp \in {"moderate", "high", "cool", "warm", "medium"}

Init ==
    /\ dsDNA = InitialDNA
    /\ templates = 0
    /\ primers = InitialPrimers
    /\ hybrids = 0
    /\ temp = "moderate"

Denature ==
    /\ temp = "moderate" \/ temp = "cool"
    /\ temp' = "high"
    /\ templates' = templates + 2 * dsDNA + hybrids
    /\ primers' = primers + hybrids
    /\ dsDNA' = 0
    /\ hybrids' = 0

Cool ==
    /\ temp = "high"
    /\ temp' = "cool"
    /\ UNCHANGED <<dsDNA, templates, primers, hybrids>>

Anneal ==
    /\ temp = "cool"
    /\ temp' = "warm"
    /\ \E n \in 0..primers:
        /\ n <= templates
        /\ hybrids' = hybrids + n
        /\ primers' = primers - n
        /\ templates' = templates - n
        /\ UNCHANGED dsDNA

Extend ==
    /\ temp = "warm"
    /\ temp' = "medium"
    /\ dsDNA' = dsDNA + hybrids
    /\ hybrids' = 0
    /\ UNCHANGED <<templates, primers>>

StartNewCycle ==
    /\ temp = "medium"
    /\ temp' = "moderate"
    /\ UNCHANGED <<dsDNA, templates, primers, hybrids>>

Next ==
    \/ Denature
    \/ Cool
    \/ Anneal
    \/ Extend
    \/ StartNewCycle

Spec == Init /\ [][Next]_vars

ConservationInvariant ==
    primers + templates + 2 * dsDNA + 2 * hybrids = InitialPrimers + 2 * InitialDNA

ConservationTemporal == []ConservationInvariant

=============================================================================