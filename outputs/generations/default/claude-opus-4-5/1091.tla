---------------------------- MODULE PCRCycle ----------------------------
EXTENDS Naturals

CONSTANTS InitPrimers, InitDNA, MaxTemp

VARIABLES temp, primers, dsDNA, ssDNA, hybrids, phase

vars == <<temp, primers, dsDNA, ssDNA, hybrids, phase>>

TypeOK ==
    /\ temp \in Nat
    /\ primers \in Nat
    /\ dsDNA \in Nat
    /\ ssDNA \in Nat
    /\ hybrids \in Nat
    /\ phase \in {"heating", "cooling", "annealing", "extension"}

Nonnegative ==
    /\ primers >= 0
    /\ dsDNA >= 0
    /\ ssDNA >= 0
    /\ hybrids >= 0

\* Conservation: total template units are preserved
\* Each dsDNA contributes 2 template strands, each ssDNA contributes 1, each hybrid contributes 1
\* Initial total = 2 * InitDNA
CountPreservation ==
    2 * dsDNA + ssDNA + hybrids = 2 * InitDNA

Init ==
    /\ temp = 25
    /\ primers = InitPrimers
    /\ dsDNA = InitDNA
    /\ ssDNA = 0
    /\ hybrids = 0
    /\ phase = "heating"

\* Heating denatures dsDNA into ssDNA (each dsDNA yields 2 ssDNA strands)
Heat ==
    /\ phase = "heating"
    /\ temp' = MaxTemp
    /\ ssDNA' = ssDNA + 2 * dsDNA
    /\ dsDNA' = 0
    /\ primers' = primers
    /\ hybrids' = hybrids
    /\ phase' = "cooling"

\* Cooling lowers temperature to allow annealing
Cool ==
    /\ phase = "cooling"
    /\ temp' = 55
    /\ primers' = primers
    /\ dsDNA' = dsDNA
    /\ ssDNA' = ssDNA
    /\ hybrids' = hybrids
    /\ phase' = "annealing"

\* Annealing: nondeterministically some primers bind to templates
\* Consumes n primers and n ssDNA templates, producing n hybrids
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

\* Extension: DNA polymerase extends hybrids into complete dsDNA
Extend ==
    /\ phase = "extension"
    /\ temp' = 72
    /\ dsDNA' = dsDNA + hybrids
    /\ hybrids' = 0
    /\ primers' = primers
    /\ ssDNA' = ssDNA
    /\ phase' = "heating"

Next ==
    \/ Heat
    \/ Cool
    \/ Anneal
    \/ Extend

Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety invariants
Safety == TypeOK /\ Nonnegative /\ CountPreservation

\* Liveness property: eventually primers are depleted
\* NOTE: This property does NOT hold because annealing can always choose n=0
EventualPrimerDepletion == <>(primers = 0)

=========================================================================