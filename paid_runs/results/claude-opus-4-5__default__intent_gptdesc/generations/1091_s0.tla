-------------------------------- MODULE PCR --------------------------------
(* 
 * Formal model of the Polymerase Chain Reaction (PCR) process
 * Captures cyclical thermocycling and mass-balance of nucleotide species
 *)

EXTENDS Naturals, Integers

CONSTANTS
    InitialDsDNA,      \* Initial count of double-stranded target molecules
    InitialPrimers,    \* Initial count of primers (pooled for simplicity)
    MaxMolecules       \* Upper bound for model checking

ASSUME InitialDsDNA \in Nat /\ InitialDsDNA > 0
ASSUME InitialPrimers \in Nat /\ InitialPrimers > 0
ASSUME MaxMolecules \in Nat /\ MaxMolecules >= InitialDsDNA + InitialPrimers

VARIABLES
    temperature,       \* Current temperature phase
    dsDNA,            \* Count of intact double-stranded DNA molecules
    ssDNA,            \* Count of single-stranded template molecules
    primers,          \* Count of available primer molecules
    hybrids,          \* Count of primer-template hybrid molecules
    cycleCount        \* Number of completed cycles

vars == <<temperature, dsDNA, ssDNA, primers, hybrids, cycleCount>>

(* Temperature phases *)
TempPhases == {"Denaturation", "Annealing", "Extension"}

(* 
 * Conservation invariant: total molecular material is conserved
 * Each dsDNA contains 2 strands worth of template material
 * Each hybrid contains 1 strand + 1 primer
 * ssDNA are single strands, primers are single primers
 * 
 * Conservation of strand material: 2*dsDNA + ssDNA + hybrids = constant (strand units)
 * Conservation of primer material: primers + hybrids = constant (when not incorporated)
 * After extension, hybrids become dsDNA, so primer material gets incorporated
 * 
 * Simplified conservation: track that nothing is created from nothing
 * Total "units" = 2*dsDNA + ssDNA + primers + 2*hybrids should relate to initial
 * 
 * Actually: Let's track separately:
 * - Strand conservation: 2*dsDNA + ssDNA + hybrids = 2*InitialDsDNA (strand count)
 * - Primer tracking: primers + hybrids + (newly synthesized strands in dsDNA beyond initial)
 *)

(* 
 * Cleaner conservation model:
 * Let BasePairs = total template strand material
 * Initially: 2*InitialDsDNA strands, InitialPrimers primers
 * 
 * During reaction:
 * - Denaturation: dsDNA -> 2 ssDNA, hybrid -> ssDNA + primer
 * - Annealing: ssDNA + primer -> hybrid
 * - Extension: hybrid -> dsDNA (consumes primer permanently into new strand)
 * 
 * Conservation: 2*dsDNA + ssDNA + hybrids + primers = 2*InitialDsDNA + InitialPrimers
 * This accounts for all molecular species at any time
 *)

TotalMaterial == 2 * dsDNA + ssDNA + hybrids + primers
InitialTotal == 2 * InitialDsDNA + InitialPrimers

TypeOK ==
    /\ temperature \in TempPhases
    /\ dsDNA \in Nat
    /\ ssDNA \in Nat
    /\ primers \in Nat
    /\ hybrids \in Nat
    /\ cycleCount \in Nat
    /\ dsDNA <= MaxMolecules
    /\ ssDNA <= MaxMolecules
    /\ primers <= MaxMolecules
    /\ hybrids <= MaxMolecules

(* Safety: Conservation invariant *)
ConservationInvariant == TotalMaterial = InitialTotal

(* Safety: All counts are non-negative (implied by Nat, but explicit) *)
NonNegativity ==
    /\ dsDNA >= 0
    /\ ssDNA >= 0
    /\ primers >= 0
    /\ hybrids >= 0

(* Combined safety invariant *)
SafetyInvariant == TypeOK /\ ConservationInvariant /\ NonNegativity

(* Initial state: all DNA is double-stranded, all primers available *)
Init ==
    /\ temperature = "Denaturation"
    /\ dsDNA = InitialDsDNA
    /\ ssDNA = 0
    /\ primers = InitialPrimers
    /\ hybrids = 0
    /\ cycleCount = 0

(* 
 * Denaturation phase actions:
 * - Breaks double-stranded DNA into single strands
 * - Breaks hybrids into single strand + primer
 * Nondeterministic: can denature some or all available dsDNA/hybrids
 *)
Denature ==
    /\ temperature = "Denaturation"
    /\ \E numDS \in 0..dsDNA, numHyb \in 0..hybrids :
        /\ numDS + numHyb > 0  \* At least something denatures (progress)
        /\ dsDNA' = dsDNA - numDS
        /\ ssDNA' = ssDNA + 2 * numDS + numHyb
        /\ hybrids' = hybrids - numHyb
        /\ primers' = primers + numHyb
        /\ UNCHANGED <<temperature, cycleCount>>

(* Transition from Denaturation to Annealing *)
TransitionToAnnealing ==
    /\ temperature = "Denaturation"
    /\ dsDNA = 0      \* All dsDNA must be denatured before moving on
    /\ hybrids = 0    \* All hybrids must be denatured
    /\ temperature' = "Annealing"
    /\ UNCHANGED <<dsDNA, ssDNA, primers, hybrids, cycleCount>>

(* 
 * Annealing phase actions:
 * - Primers bind to single-stranded templates forming hybrids
 * - Bounded by availability of both primers and ssDNA
 * Nondeterministic: can form some number of hybrids up to min(primers, ssDNA)
 *)
Anneal ==
    /\ temperature = "Annealing"
    /\ primers > 0
    /\ ssDNA > 0
    /\ \E numAnneal \in 1..primers :
        /\ numAnneal <= ssDNA
        /\ primers' = primers - numAnneal
        /\ ssDNA' = ssDNA - numAnneal
        /\ hybrids' = hybrids + numAnneal
        /\ UNCHANGED <<temperature, dsDNA, cycleCount>>

(* Transition from Annealing to Extension *)
TransitionToExtension ==
    /\ temperature = "Annealing"
    /\ temperature' = "Extension"
    /\ UNCHANGED <<dsDNA, ssDNA, primers, hybrids, cycleCount>>

(* 
 * Extension phase actions:
 * - Polymerase extends primers on hybrids, creating new dsDNA
 * - Each hybrid becomes one dsDNA (primer is incorporated)
 * Nondeterministic: can extend some or all hybrids
 *)
Extend ==
    /\ temperature = "Extension"
    /\ hybrids > 0
    /\ \E numExtend \in 1..hybrids :
        /\ hybrids' = hybrids - numExtend
        /\ dsDNA' = dsDNA + numExtend
        /\ UNCHANGED <<temperature, ssDNA, primers, cycleCount>>

(* Transition from Extension back to Denaturation (complete cycle) *)
TransitionToDenaturation ==
    /\ temperature = "Extension"
    /\ temperature' = "Denaturation"
    /\ cycleCount' = cycleCount + 1
    /\ UNCHANGED <<dsDNA, ssDNA, primers, hybrids>>

(* 
 * Skip annealing if no primers available (primer depletion scenario)
 * This allows the cycle to continue even without amplification
 *)
SkipAnnealingNoPrimers ==
    /\ temperature = "Annealing"
    /\ primers = 0
    /\ temperature' = "Extension"
    /\ UNCHANGED <<dsDNA, ssDNA, primers, hybrids, cycleCount>>

(* 
 * Skip annealing if no ssDNA available 
 *)
SkipAnnealingNoTemplate ==
    /\ temperature = "Annealing"
    /\ ssDNA = 0
    /\ temperature' = "Extension"
    /\ UNCHANGED <<dsDNA, ssDNA, primers, hybrids, cycleCount>>

(* 
 * Skip extension if no hybrids to extend
 *)
SkipExtensionNoHybrids ==
    /\ temperature = "Extension"
    /\ hybrids = 0
    /\ temperature' = "Denaturation"
    /\ cycleCount' = cycleCount + 1
    /\ UNCHANGED <<dsDNA, ssDNA, primers, hybrids>>

(* Next state relation: nondeterministic choice among enabled actions *)
Next ==
    \/ Denature
    \/ TransitionToAnnealing
    \/ Anneal
    \/ TransitionToExtension
    \/ Extend
    \/ TransitionToDenaturation
    \/ SkipAnnealingNoPrimers
    \/ SkipAnnealingNoTemplate
    \/ SkipExtensionNoHybrids

(* Fairness: ensure progress through cycles *)
Fairness ==
    /\ WF_vars(TransitionToAnnealing)
    /\ WF_vars(TransitionToExtension)
    /\ WF_vars(TransitionToDenaturation)
    /\ WF_vars(SkipAnnealingNoPrimers)
    /\ WF_vars(SkipAnnealingNoTemplate)
    /\ WF_vars(SkipExtensionNoHybrids)
    /\ SF_vars(Denature)
    /\ SF_vars(Anneal)
    /\ SF_vars(Extend)

(* Full specification with fairness *)
Spec == Init /\ [][Next]_vars /\ Fairness

(* ----- PROPERTIES ----- *)

(* Liveness: cycles continue forever *)
AlwaysEventuallyCycle == []<>(cycleCount' > cycleCount)

(* Liveness: if primers available and templates exist, eventually more dsDNA produced *)
EventualAmplification ==
    (primers >= 2 /\ ssDNA >= 2) ~> (dsDNA > InitialDsDNA)

(* Property: primer depletion is possible *)
PrimerDepletionPossible == <>(primers = 0)

(* Property: amplification occurred at some point *)
AmplificationOccurred == <>(dsDNA > InitialDsDNA)

(* Temperature is always in valid phase *)
ValidTemperature == temperature \in TempPhases

(* Cycles always increment (never decrease) *)
CyclesMonotonic == [][cycleCount' >= cycleCount]_vars

(* Combined invariant for model checking *)
Invariant == SafetyInvariant /\ ValidTemperature

=============================================================================