------------------------------- MODULE PCR -------------------------------
EXTENDS Naturals, TLC

CONSTANTS 
    InitialPrimerStock,
    InitialDoubleStrandedDNAStock

VARIABLES 
    DoubleStrandedDNA,
    SingleStrandedTemplates,
    Primers,
    TemplatePrimerHybrids

Init == 
    /\ DoubleStrandedDNA = InitialDoubleStrandedDNAStock
    /\ SingleStrandedTemplates = 0
    /\ Primers = InitialPrimerStock
    /\ TemplatePrimerHybrids = 0

HighHeat ==
    /\ DoubleStrandedDNA' = 0
    /\ SingleStrandedTemplates' = DoubleStrandedDNA + 2 * TemplatePrimerHybrids
    /\ Primers' = Primers + TemplatePrimerHybrids
    /\ TemplatePrimerHybrids' = 0

Cooling ==
    /\ UNCHANGED <<DoubleStrandedDNA, SingleStrandedTemplates, Primers, TemplatePrimerHybrids>>

Annealing ==
    /\ DoubleStrandedDNA' = DoubleStrandedDNA
    /\ SingleStrandedTemplates' = SingleStrandedTemplates - x
    /\ Primers' = Primers - x
    /\ TemplatePrimerHybrids' = TemplatePrimerHybrids + x
    /\ 0 <= x <= MIN(SingleStrandedTemplates, Primers)

MediumHeat ==
    /\ DoubleStrandedDNA' = DoubleStrandedDNA + TemplatePrimerHybrids
    /\ SingleStrandedTemplates' = SingleStrandedTemplates
    /\ Primers' = Primers
    /\ TemplatePrimerHybrids' = 0

Next == 
    \/ HighHeat
    \/ Cooling
    \/ Annealing
    \/ MediumHeat

Spec ==
    /\ Init
    /\ [][Next]_<<DoubleStrandedDNA, SingleStrandedTemplates, Primers, TemplatePrimerHybrids>>
    /\ WF_next(<<HighHeat, Cooling, Annealing, MediumHeat>>)

ConservationInvariant ==
    Primers + SingleStrandedTemplates + 2 * DoubleStrandedDNA + 2 * TemplatePrimerHybrids = InitialPrimerStock + 2 * InitialDoubleStrandedDNAStock

TemporalConservationProperty ==
    [](Primers + SingleStrandedTemplates + 2 * DoubleStrandedDNA + 2 * TemplatePrimerHybrids = InitialPrimerStock + 2 * InitialDoubleStrandedDNAStock)

=============================================================================