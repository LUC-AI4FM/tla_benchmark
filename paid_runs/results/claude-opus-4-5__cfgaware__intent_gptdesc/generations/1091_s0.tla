---------------------------- MODULE PCR ----------------------------

EXTENDS Naturals, Integers

CONSTANTS
    InitDoubleStrands,
    InitTemplates,
    InitPrimers,
    MaxPrimersPerStep

VARIABLES
    temperature,
    doubleStrands,
    templates,
    primers,
    hybrids,
    cycleCount

vars == <<temperature, doubleStrands, templates, primers, hybrids, cycleCount>>

\* Temperature phases
Temperatures == {"denaturation", "annealing", "extension"}

\* Initial total molecular units for conservation law
\* Double strands contain 2 template units worth of material
\* Hybrids contain 1 template + 1 primer worth of material
InitialTotal == 2 * InitDoubleStrands + InitTemplates + InitPrimers

\* Current total molecular units (conservation invariant)
CurrentTotal == 2 * doubleStrands + templates + primers + 2 * hybrids

\* Type invariant
TypeOK ==
    /\ temperature \in Temperatures
    /\ doubleStrands \in Nat
    /\ templates \in Nat
    /\ primers \in Nat
    /\ hybrids \in Nat
    /\ cycleCount \in Nat

\* Non-negativity of primer count (specific safety property)
primerPositive == primers >= 0

\* Conservation of molecular material
preservationInvariant == CurrentTotal = InitialTotal

\* Preservation as a temporal property (always holds)
preservationProperty == []preservationInvariant

\* Initial state
Init ==
    /\ temperature = "denaturation"
    /\ doubleStrands = InitDoubleStrands
    /\ templates = InitTemplates
    /\ primers = InitPrimers
    /\ hybrids = 0
    /\ cycleCount = 0

\* Denaturation phase: break double strands and hybrids into single strands
\* Double strands become 2 templates
\* Hybrids release 1 template and 1 primer
Denature ==
    /\ temperature = "denaturation"
    /\ templates' = templates + 2 * doubleStrands + hybrids
    /\ primers' = primers + hybrids
    /\ doubleStrands' = 0
    /\ hybrids' = 0
    /\ cycleCount' = cycleCount
    /\ temperature' = "annealing"

\* Annealing phase: primers bind to templates forming hybrids
\* Nondeterministically choose how many annealments occur (bounded by availability)
Anneal ==
    /\ temperature = "annealing"
    /\ \E n \in 0..MaxPrimersPerStep :
        /\ n <= primers
        /\ n <= templates
        /\ primers' = primers - n
        /\ templates' = templates - n
        /\ hybrids' = hybrids + n
        /\ doubleStrands' = doubleStrands
        /\ cycleCount' = cycleCount
        /\ temperature' = "extension"

\* Extension phase: hybrids are extended to form new double strands
Extend ==
    /\ temperature = "extension"
    /\ doubleStrands' = doubleStrands + hybrids
    /\ hybrids' = 0
    /\ templates' = templates
    /\ primers' = primers
    /\ cycleCount' = cycleCount + 1
    /\ temperature' = "denaturation"

\* Next state relation
Next ==
    \/ Denature
    \/ Anneal
    \/ Extend

\* Fairness conditions for liveness
Fairness ==
    /\ WF_vars(Denature)
    /\ WF_vars(Anneal)
    /\ WF_vars(Extend)

\* Complete specification with fairness
Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: all counts are non-negative
NonNegativity ==
    /\ doubleStrands >= 0
    /\ templates >= 0
    /\ primers >= 0
    /\ hybrids >= 0

\* Combined safety invariant
Safety == TypeOK /\ NonNegativity /\ preservationInvariant

\* Liveness: cycles can always progress (system doesn't deadlock)
CycleProgress == []<>(cycleCount' > cycleCount)

\* Eventually more double strands can be produced (if resources available)
EventualAmplification ==
    (InitPrimers > 0 /\ (InitDoubleStrands > 0 \/ InitTemplates > 0))
        => <>(doubleStrands > InitDoubleStrands)

\* Primer depletion detection
PrimerDepleted == primers = 0

\* If primers deplete, no more annealing can consume primers
DepletionConsequence ==
    [](PrimerDepleted => [](primers = 0 \/ primers' >= primers))

=============================================================================