------------------------- MODULE PCR -------------------------
EXTENDS Integers, TLC

CONSTANTS InitialDNA, InitialPrimers

ASSUME InitialDNA \in Nat /\ InitialPrimers \in Nat

VARIABLES dna, templates, hybrids, primers, phase

vars == <<dna, templates, hybrids, primers, phase>>

TypeOK ==
    /\ dna \in Nat
    /\ templates \in Nat
    /\ hybrids \in Nat
    /\ primers \in Nat
    /\ phase \in {"heating", "cooling", "annealing", "extension"}

primerPositive == primers >= 0

\* A weighted sum of the molecule counts that is preserved by the system dynamics.
PreservedCount == (2 * dna) + templates + (2 * hybrids) + primers

preservationInvariant == PreservedCount = (2 * InitialDNA) + InitialPrimers

preservationProperty == [](preservationInvariant)

Init ==
    /\ dna = InitialDNA
    /\ templates = 0
    /\ hybrids = 0
    /\ primers = InitialPrimers
    /\ phase = "heating"

\* Heating denatures double-stranded DNA into single-stranded templates.
\* If there is no DNA, the system just moves to the next phase.
Heat ==
    /\ phase = "heating"
    /\ IF dna > 0
       THEN /\ dna' = 0
            /\ templates' = templates + (2 * dna)
            /\ UNCHANGED <<hybrids, primers>>
       ELSE UNCHANGED <<dna, templates, hybrids, primers>>
    /\ phase' = "cooling"

\* Cooling prepares the system for primer annealing.
Cool ==
    /\ phase = "cooling"
    /\ phase' = "annealing"
    /\ UNCHANGED <<dna, templates, hybrids, primers>>

\* Primers anneal to templates, forming hybrids. A nondeterministic number
\* of available primers and templates are consumed. If none are available,
\* the system moves to the next phase.
Anneal ==
    /\ phase = "annealing"
    /\ IF primers > 0 /\ templates > 0
       THEN \E k \in 1..Min(primers, templates):
                /\ primers' = primers - k
                /\ templates' = templates - k
                /\ hybrids' = hybrids + k
                /\ UNCHANGED <<dna>>
       ELSE UNCHANGED <<dna, templates, hybrids, primers>>
    /\ phase' = "extension"

\* DNA polymerase extends the primers, converting hybrids into new
\* double-stranded DNA. If there are no hybrids, the system moves to the
\* next phase.
Extend ==
    /\ phase = "extension"
    /\ IF hybrids > 0
       THEN /\ dna' = dna + hybrids
            /\ hybrids' = 0
            /\ UNCHANGED <<templates, primers>>
       ELSE UNCHANGED <<dna, templates, hybrids, primers>>
    /\ phase' = "heating"

Next == Heat \/ Cool \/ Anneal \/ Extend

Spec == Init /\ [][Next]_vars

\* Liveness property: eventually all primers are consumed.
\* This property does not hold. The system can reach a state where templates
\* are depleted, after which no more primers can be consumed, even if
\* primers are still available.
PrimerDepletion == <>(primers = 0)

=============================================================================