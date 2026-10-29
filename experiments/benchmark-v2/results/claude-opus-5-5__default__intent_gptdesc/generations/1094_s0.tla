---------------------------- MODULE PCRAmplification ----------------------------
EXTENDS Naturals

CONSTANTS
    InitPrimers,     \* finite initial pool of free primers (never replenished)
    InitTemplates    \* initial number of double-stranded templates

ASSUME InitPrimers \in Nat
ASSUME InitTemplates \in Nat

VARIABLES
    ds,          \* number of double-stranded molecules
    ss,          \* number of free single strands
    primers,     \* number of free primers
    hybrids,     \* number of primer-template hybrids
    temp,        \* current discrete temperature mode
    cycles,      \* number of completed amplification cycles
    lastPhase    \* ghost variable: kind of the most recent step

vars   == <<ds, ss, primers, hybrids, temp, cycles, lastPhase>>
counts == <<ds, ss, primers, hybrids>>

Temps  == {"HOT", "COOL", "WARM"}
Phases == {"Init", "Denature", "Anneal", "Extend", "Flip"}

\* The only legal temperature flips: HOT -> COOL -> WARM -> HOT
LegalFlips == { <<"HOT", "COOL">>, <<"COOL", "WARM">>, <<"WARM", "HOT">> }

Min(a, b) == IF a <= b THEN a ELSE b

-----------------------------------------------------------------------------
Init ==
    /\ ds = InitTemplates
    /\ ss = 0
    /\ primers = InitPrimers
    /\ hybrids = 0
    /\ temp = "HOT"
    /\ cycles = 0
    /\ lastPhase = "Init"

\* Denaturation at high temperature: double strands melt into two single
\* strands each; hybrids melt into a single strand plus a returned primer.
Denature ==
    /\ temp = "HOT"
    /\ ds > 0 \/ hybrids > 0
    /\ ss' = ss + 2 * ds + hybrids
    /\ primers' = primers + hybrids
    /\ ds' = 0
    /\ hybrids' = 0
    /\ lastPhase' = "Denature"
    /\ UNCHANGED <<temp, cycles>>

\* Annealing at low temperature: k primers bind to k single strands,
\* bounded by available primers and available templates.
AnnealCond == temp = "COOL" /\ primers > 0 /\ ss > 0

Anneal ==
    /\ AnnealCond
    /\ \E k \in 1..Min(primers, ss) :
          /\ primers' = primers - k
          /\ ss' = ss - k
          /\ hybrids' = hybrids + k
    /\ lastPhase' = "Anneal"
    /\ UNCHANGED <<ds, temp, cycles>>

\* Extension at warm temperature: every hybrid becomes a new double strand.
\* Completing extension completes one amplification cycle.
Extend ==
    /\ temp = "WARM"
    /\ hybrids > 0
    /\ ds' = ds + hybrids
    /\ hybrids' = 0
    /\ cycles' = cycles + 1
    /\ lastPhase' = "Extend"
    /\ UNCHANGED <<ss, primers, temp>>

\* Intermediate temperature flips: change only the temperature, and only
\* once the phase at the current temperature has run to completion.
FlipHotToCool ==
    /\ temp = "HOT"
    /\ ds = 0
    /\ hybrids = 0
    /\ temp' = "COOL"
    /\ lastPhase' = "Flip"
    /\ UNCHANGED <<ds, ss, primers, hybrids, cycles>>

FlipCoolToWarm ==
    /\ temp = "COOL"
    /\ ~AnnealCond
    /\ temp' = "WARM"
    /\ lastPhase' = "Flip"
    /\ UNCHANGED <<ds, ss, primers, hybrids, cycles>>

FlipWarmToHot ==
    /\ temp = "WARM"
    /\ hybrids = 0
    /\ temp' = "HOT"
    /\ lastPhase' = "Flip"
    /\ UNCHANGED <<ds, ss, primers, hybrids, cycles>>

Flip == FlipHotToCool \/ FlipCoolToWarm \/ FlipWarmToHot

Next ==
    \/ Denature
    \/ Anneal
    \/ Extend
    \/ Flip

Fairness ==
    /\ WF_vars(Denature)
    /\ WF_vars(Anneal)
    /\ WF_vars(Extend)
    /\ WF_vars(FlipHotToCool)
    /\ WF_vars(FlipCoolToWarm)
    /\ WF_vars(FlipWarmToHot)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* (1) Counts never go negative and all variables stay in their domains.
TypeOK ==
    /\ ds \in Nat
    /\ ss \in Nat
    /\ primers \in Nat
    /\ hybrids \in Nat
    /\ temp \in Temps
    /\ cycles \in Nat
    /\ lastPhase \in Phases

\* Conservation of strands: every strand is either an original template
\* strand or was synthesised from a primer that has been permanently consumed.
StrandConservation ==
    2 * ds + ss + hybrids = 2 * InitTemplates + (InitPrimers - primers - hybrids)

\* Primer accounting: primers are free, in hybrids, or incorporated.
PrimerConservation ==
    primers + hybrids <= InitPrimers

\* Hybrids never persist at high temperature.
NoHybridsWhenHot == temp = "HOT" => hybrids = 0

\* (6) Each completed cycle permanently incorporated at least one primer.
CyclesBounded == cycles <= InitPrimers - primers - hybrids

Invariants ==
    /\ TypeOK
    /\ StrandConservation
    /\ PrimerConservation
    /\ NoHybridsWhenHot
    /\ CyclesBounded

\* (2) Free primers never increase except when returned by denaturation.
PrimerMonotone ==
    [][ primers' > primers =>
          /\ temp = "HOT"
          /\ lastPhase' = "Denature"
          /\ primers' = primers + hybrids
          /\ hybrids' = 0 ]_vars

\* Primer use reduces free primer by exactly the number of new hybrids.
AnnealConservation ==
    [][ lastPhase' = "Anneal" =>
          /\ primers - primers' = hybrids' - hybrids
          /\ ss - ss' = hybrids' - hybrids
          /\ hybrids' > hybrids ]_vars

\* (3) Extension increases double-stranded material by at most the number of
\*     currently formed hybrids (exactly the number consumed).
ExtensionBound ==
    [][ ds' > ds =>
          /\ temp = "WARM"
          /\ ds' - ds <= hybrids
          /\ ds' - ds = hybrids - hybrids' ]_vars

\* (4a) No temperature transition can produce an illegal state change:
\*      temperature changes only along legal flips and nothing else changes.
LegalTemperatureChanges ==
    [][ temp' # temp =>
          /\ <<temp, temp'>> \in LegalFlips
          /\ UNCHANGED <<ds, ss, primers, hybrids, cycles>> ]_vars

\* (6) The cycle counter increments exactly when an extension phase completes.
CycleCounterAccurate ==
    [][ /\ cycles' = cycles + (IF lastPhase' = "Extend" THEN 1 ELSE 0)
        /\ (lastPhase' = "Extend" => hybrids' = 0) ]_vars

\* (4b) Every enabled annealing eventually occurs.
AnnealEventuallyOccurs ==
    [](AnnealCond => <><<Anneal>>_vars)

\* (5) With a finite primer pool and no replenishment, continued cycling
\*     eventually depletes the free primers.
PrimersEventuallyDepleted ==
    (InitTemplates > 0) => <>[](primers = 0)

\* Each phase eventually happens when continuously enabled (progress).
ExtensionEventuallyOccurs ==
    []((temp = "WARM" /\ hybrids > 0) => <><<Extend>>_vars)

DenaturationEventuallyOccurs ==
    []((temp = "HOT" /\ (ds > 0 \/ hybrids > 0)) => <><<Denature>>_vars)

=============================================================================