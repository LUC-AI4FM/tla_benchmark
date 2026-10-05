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

primerPositive == primers >= 0

\* Conservation: primers + templates + 2*dsDNA + 2*hybrids = InitialPrimers + 2*InitialDNA
preservationInvariant ==
    primers + templates + 2*dsDNA + 2*hybrids = InitialPrimers + 2*InitialDNA

preservationProperty == []preservationInvariant

Init ==
    /\ dsDNA = InitialDNA
    /\ templates = 0
    /\ primers = InitialPrimers
    /\ hybrids = 0
    /\ temp = "moderate"

\* Denaturation: dsDNA and hybrids denature into single-stranded templates
\* Each dsDNA produces 2 templates, each hybrid produces 1 template and releases 1 primer
Denature ==
    /\ temp = "moderate"
    /\ dsDNA' = 0
    /\ templates' = templates + 2*dsDNA + hybrids
    /\ primers' = primers + hybrids
    /\ hybrids' = 0
    /\ temp' = "high"

\* Cooling: transition from high to cool (ready for annealing)
Cool ==
    /\ temp = "high"
    /\ dsDNA' = dsDNA
    /\ templates' = templates
    /\ primers' = primers
    /\ hybrids' = hybrids
    /\ temp' = "cool"

\* Transition to warm temperature for annealing
ToWarm ==
    /\ temp = "cool"
    /\ dsDNA' = dsDNA
    /\ templates' = templates
    /\ primers' = primers
    /\ hybrids' = hybrids
    /\ temp' = "warm"

\* Annealing: some nondeterministic number of primers anneal to templates forming hybrids
\* Each annealing consumes 1 primer and 1 template to form 1 hybrid
Anneal ==
    /\ temp = "warm"
    /\ \E n \in 0..primers:
        /\ n <= templates
        /\ primers' = primers - n
        /\ templates' = templates - n
        /\ hybrids' = hybrids + n
        /\ dsDNA' = dsDNA
    /\ temp' = "medium"

\* Extension: polymerase extends all hybrids into new double-stranded DNA
\* Each hybrid becomes 1 dsDNA
Extend ==
    /\ temp = "medium"
    /\ dsDNA' = dsDNA + hybrids
    /\ hybrids' = 0
    /\ templates' = templates
    /\ primers' = primers
    /\ temp' = "moderate"

Next ==
    \/ Denature
    \/ Cool
    \/ ToWarm
    \/ Anneal
    \/ Extend

Spec == Init /\ [][Next]_vars

=========================================================================