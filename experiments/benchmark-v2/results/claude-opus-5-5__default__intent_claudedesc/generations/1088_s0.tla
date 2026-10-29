------------------------------- MODULE PCR -------------------------------
(***************************************************************************)
(* A model of DNA amplification by the Polymerase Chain Reaction (PCR).   *)
(*                                                                         *)
(* Molecular species (counts):                                             *)
(*   dna      - double-stranded target DNA (2 strand units each)           *)
(*   template - single-stranded template DNA (1 strand unit each)          *)
(*   primer   - free short primers (1 unit each)                           *)
(*   hybrid   - primer-template complexes (template + primer = 2 units)    *)
(*                                                                         *)
(* Reactions:                                                              *)
(*   Denature : dna             -> 2 template   (high temperature)         *)
(*   Anneal   : template+primer -> hybrid       (low temperature)          *)
(*   Extend   : hybrid          -> dna          (medium temperature)       *)
(*                                                                         *)
(* Thermal cycling: denature -> anneal -> extend -> denature -> ...        *)
(* A phase ends only when its reaction can no longer proceed.              *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    PRIMER_INIT,   \* number of primers initially added
    DNA_INIT,      \* number of double-stranded target DNA molecules added
    MaxCycles      \* bound on the number of thermal cycles

ASSUME PRIMER_INIT \in Nat
ASSUME DNA_INIT \in Nat
ASSUME MaxCycles \in Nat

VARIABLES
    primer,     \* free primers
    template,   \* single-stranded templates
    hybrid,     \* primer-template hybrids
    dna,        \* double-stranded DNA
    stage,      \* current thermal phase
    cycle       \* number of completed or started cycles

vars == <<primer, template, hybrid, dna, stage, cycle>>

Stages == {"init", "denature", "anneal", "extend"}

\* Total material, measured in strand units
Mass == primer + template + 2 * hybrid + 2 * dna

InitialMass == PRIMER_INIT + 2 * DNA_INIT

---------------------------------------------------------------------------
Init ==
    /\ primer   = PRIMER_INIT
    /\ template = 0
    /\ hybrid   = 0
    /\ dna      = DNA_INIT
    /\ stage    = "init"
    /\ cycle    = 0

(***************************************************************************)
(* Thermal transitions (temperature changes)                               *)
(***************************************************************************)
\* Heat to denaturation temperature: starts a new cycle
Heat ==
    /\ stage \in {"init", "extend"}
    /\ (stage = "extend" => hybrid = 0)       \* extension complete
    /\ cycle < MaxCycles
    /\ stage' = "denature"
    /\ cycle' = cycle + 1
    /\ UNCHANGED <<primer, template, hybrid, dna>>

\* Cool to annealing temperature once all DNA is denatured
Cool ==
    /\ stage = "denature"
    /\ dna = 0
    /\ stage' = "anneal"
    /\ UNCHANGED <<primer, template, hybrid, dna, cycle>>

\* Warm to extension temperature once annealing can no longer proceed
Warm ==
    /\ stage = "anneal"
    /\ (template = 0 \/ primer = 0)
    /\ stage' = "extend"
    /\ UNCHANGED <<primer, template, hybrid, dna, cycle>>

(***************************************************************************)
(* Biochemical reactions                                                   *)
(***************************************************************************)
Denature ==
    /\ stage = "denature"
    /\ dna > 0
    /\ dna'      = dna - 1
    /\ template' = template + 2
    /\ UNCHANGED <<primer, hybrid, stage, cycle>>

Anneal ==
    /\ stage = "anneal"
    /\ template > 0
    /\ primer > 0
    /\ template' = template - 1
    /\ primer'   = primer - 1
    /\ hybrid'   = hybrid + 1
    /\ UNCHANGED <<dna, stage, cycle>>

Extend ==
    /\ stage = "extend"
    /\ hybrid > 0
    /\ hybrid' = hybrid - 1
    /\ dna'    = dna + 1
    /\ UNCHANGED <<primer, template, stage, cycle>>

\* Process finished: cycle limit reached after the final extension
Done ==
    /\ stage = "extend"
    /\ hybrid = 0
    /\ cycle = MaxCycles
    /\ UNCHANGED vars

Step == Heat \/ Cool \/ Warm \/ Denature \/ Anneal \/ Extend

Next == Step \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

---------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
TypeOK ==
    /\ primer   \in Nat
    /\ template \in Nat
    /\ hybrid   \in Nat
    /\ dna      \in Nat
    /\ stage    \in Stages
    /\ cycle    \in 0..MaxCycles

\* Non-negativity of all molecular species
NonNegative ==
    /\ primer   >= 0
    /\ template >= 0
    /\ hybrid   >= 0
    /\ dna      >= 0

\* Conservation of mass
Conservation == Mass = InitialMass

\* Phase-specific species constraints
PhaseConsistency ==
    /\ stage = "anneal" => dna = 0
    /\ stage = "extend" => dna = 0 \/ template = 0 \/ primer = 0
    /\ stage = "init"   => hybrid = 0 /\ template = 0

Inv == TypeOK /\ NonNegative /\ Conservation /\ PhaseConsistency

\* Proper sequencing: each reaction occurs only in its thermal phase,
\* and phases advance in the order denature -> anneal -> extend -> denature
ReactionInPhase ==
    [][ /\ (dna' < dna /\ template' > template) => stage = "denature"
        /\ hybrid' > hybrid => stage = "anneal"
        /\ (hybrid' < hybrid /\ dna' > dna) => stage = "extend" ]_vars

PhaseOrder ==
    [][ stage' # stage =>
          \/ (stage \in {"init", "extend"} /\ stage' = "denature")
          \/ (stage = "denature" /\ stage' = "anneal")
          \/ (stage = "anneal"   /\ stage' = "extend") ]_vars

CycleMonotone == [][cycle' >= cycle]_vars

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)
\* With sufficient primers, the target DNA count eventually exceeds
\* its initial amount.
AmplificationProgress ==
    (DNA_INIT > 0 /\ PRIMER_INIT > DNA_INIT /\ MaxCycles > 0)
        => <>(dna > DNA_INIT)

\* With sufficient primers, each complete cycle doubles the DNA.
CycleDoubling ==
    \A k \in 1..InitialMass :
        ( /\ stage \in {"init", "extend"}
          /\ hybrid = 0 /\ template = 0
          /\ dna = k
          /\ primer >= 2 * k
          /\ cycle < MaxCycles )
        ~> (dna = 2 * k)

\* The process eventually terminates in the final extension phase.
Termination == <>(stage = "extend" /\ hybrid = 0 /\ cycle = MaxCycles)
                \/ (MaxCycles = 0)

THEOREM Spec => []Inv
THEOREM Spec => ReactionInPhase /\ PhaseOrder /\ CycleMonotone
THEOREM Spec => AmplificationProgress /\ CycleDoubling
=============================================================================