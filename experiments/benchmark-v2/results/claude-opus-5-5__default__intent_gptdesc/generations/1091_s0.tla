---------------------------- MODULE PCRAmplification ----------------------------
(***************************************************************************)
(* Abstract model of the polymerase chain reaction (PCR).                  *)
(*                                                                         *)
(* Species tracked (all counts are natural numbers):                       *)
(*   ds      : intact double-stranded target molecules (2 strands each)    *)
(*   ss      : free single-stranded templates (1 strand each)              *)
(*   primers : free primers (a single pooled primer count)                 *)
(*   hybrid  : primer-template hybrids (1 template strand + 1 primer)      *)
(*                                                                         *)
(* Thermocycling phases: "Denature" (high), "Anneal" (low),                *)
(* "Extend" (intermediate). A cycle is Denature -> Anneal -> Extend.       *)
(*                                                                         *)
(* Mass balance. Count "strand-or-primer units", where a primer that is    *)
(* extended becomes a full strand:                                         *)
(*      2*ds + ss + 2*hybrid + primers  =  Total                           *)
(*   Anneal : ss-1, primers-1, hybrid+1        (-1 -1 +2 = 0)              *)
(*   Extend : hybrid-1, ds+1                   (-2 +2    = 0)              *)
(*   Melt ds: ds-1, ss+2                       (-2 +2    = 0)              *)
(*   Melt hy: hybrid-1, ss+1, primers+1        (-2 +1 +1 = 0)              *)
(*                                                                         *)
(* The number of molecules processed in each step is chosen               *)
(* nondeterministically, bounded only by availability. The model does not *)
(* fix how many steps occur within a phase.                                *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    InitDS,       \* initial number of double-stranded targets
    InitSS,       \* initial number of free single-stranded templates
    InitPrimers,  \* initial number of (pooled) primers
    MaxCycles     \* cap on the cycle counter (keeps the state space finite)

ASSUME /\ InitDS \in Nat
       /\ InitSS \in Nat
       /\ InitPrimers \in Nat
       /\ MaxCycles \in Nat \ {0}

VARIABLES temp, ds, ss, primers, hybrid, cycle

vars == <<temp, ds, ss, primers, hybrid, cycle>>

Phases == {"Denature", "Anneal", "Extend"}

Min(a, b) == IF a <= b THEN a ELSE b

\* Weighted linear measure of the nucleotide-containing material.
Mass == 2 * ds + ss + 2 * hybrid + primers

Total == 2 * InitDS + InitSS + InitPrimers

\* Total number of full-length strands, whether free or paired.
Strands == 2 * ds + ss + hybrid

-----------------------------------------------------------------------------
Init ==
    /\ temp    = "Denature"
    /\ ds      = InitDS
    /\ ss      = InitSS
    /\ primers = InitPrimers
    /\ hybrid  = 0
    /\ cycle   = 0

(***************************************************************************)
(* Denaturation at high temperature. Some double strands and/or hybrids    *)
(* melt. Melting a hybrid frees its template strand and its primer.        *)
(***************************************************************************)
Melt ==
    /\ temp = "Denature"
    /\ \E a \in 0..ds, b \in 0..hybrid :
          /\ a + b > 0
          /\ ds'      = ds - a
          /\ hybrid'  = hybrid - b
          /\ ss'      = ss + 2 * a + b
          /\ primers' = primers + b
    /\ UNCHANGED <<temp, cycle>>

(***************************************************************************)
(* Annealing at low temperature. Some number k of primers bind to k free   *)
(* templates, where k is bounded by the availability of both.              *)
(***************************************************************************)
Anneal ==
    /\ temp = "Anneal"
    /\ \E k \in 1..Min(ss, primers) :
          /\ ss'      = ss - k
          /\ primers' = primers - k
          /\ hybrid'  = hybrid + k
    /\ UNCHANGED <<temp, ds, cycle>>

(***************************************************************************)
(* Extension at intermediate temperature. The polymerase extends some      *)
(* number k of hybrids, each becoming a new double-stranded molecule.      *)
(***************************************************************************)
Extend ==
    /\ temp = "Extend"
    /\ \E k \in 1..hybrid :
          /\ hybrid' = hybrid - k
          /\ ds'     = ds + k
    /\ UNCHANGED <<temp, ss, primers, cycle>>

(***************************************************************************)
(* Temperature transitions. Leaving the denaturation phase requires that   *)
(* denaturation be complete, since nothing stays paired at high heat.      *)
(***************************************************************************)
Cool ==
    /\ temp = "Denature"
    /\ ds = 0
    /\ hybrid = 0
    /\ temp' = "Anneal"
    /\ UNCHANGED <<ds, ss, primers, hybrid, cycle>>

Warm ==
    /\ temp = "Anneal"
    /\ temp' = "Extend"
    /\ UNCHANGED <<ds, ss, primers, hybrid, cycle>>

Heat ==
    /\ temp = "Extend"
    /\ temp' = "Denature"
    /\ cycle' = IF cycle < MaxCycles THEN cycle + 1 ELSE cycle
    /\ UNCHANGED <<ds, ss, primers, hybrid>>

PhaseChange == Cool \/ Warm \/ Heat

Next == Melt \/ Anneal \/ Extend \/ PhaseChange

(***************************************************************************)
(* Fairness                                                                *)
(* - Weak fairness on phase changes and on melting makes cycling continue. *)
(*   Melting is required before Cool can fire, so this ensures that        *)
(*   denaturation always completes.                                        *)
(* - Strong fairness on Anneal and Extend means that if annealing or       *)
(*   extension is possible in infinitely many phases, it eventually        *)
(*   happens.                                                              *)
(***************************************************************************)
Fairness ==
    /\ WF_vars(Melt)
    /\ WF_vars(PhaseChange)
    /\ SF_vars(Anneal)
    /\ SF_vars(Extend)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(*************************** Safety properties *****************************)

TypeOK ==
    /\ temp \in Phases
    /\ ds \in Nat
    /\ ss \in Nat
    /\ primers \in Nat
    /\ hybrid \in Nat
    /\ cycle \in 0..MaxCycles

NonNegative ==
    /\ ds >= 0
    /\ ss >= 0
    /\ primers >= 0
    /\ hybrid >= 0

TempInPhases == temp \in Phases

Conservation == Mass = Total

SafetyInv == TypeOK /\ NonNegative /\ TempInPhases /\ Conservation

\* Primers are never created. Free primers plus bound primers never increase.
PrimerPoolNonIncreasing ==
    [][primers' + hybrid' <= primers + hybrid]_vars

\* Strands are never destroyed.
StrandsNonDecreasing ==
    [][Strands' >= Strands]_vars

(***************************************************************************)
(* Consequence of primer depletion: once no primer is free or bound, the   *)
(* total number of strands is frozen and no further amplification occurs. *)
(***************************************************************************)
DepletionStopsAmplification ==
    [][(primers = 0 /\ hybrid = 0) => (Strands' = Strands)]_vars

DepletionIsPermanent ==
    [][(primers = 0 /\ hybrid = 0) => (primers' = 0 /\ hybrid' = 0)]_vars

(***************************************************************************)
(* Witness for depletion. This invariant is expected to be VIOLATED when   *)
(* primers are limited. TLC's counterexample then exhibits a primer        *)
(* depletion trace.                                                        *)
(***************************************************************************)
NeverDepleted == primers + hybrid > 0

\* Witness for bounded amplification. Expected to be violated when amplification occurs.
NoAmplification == Strands <= 2 * InitDS + InitSS

(*************************** Liveness properties ***************************)

\* Thermocycling continues forever: every phase recurs infinitely often.
InfiniteCycling ==
    /\ []<>(temp = "Denature")
    /\ []<>(temp = "Anneal")
    /\ []<>(temp = "Extend")

\* The cycle counter eventually reaches its cap.
CyclesProgress == <>(cycle = MaxCycles)

(***************************************************************************)
(* With at least one primer and at least one template-bearing molecule,    *)
(* additional double-stranded product is eventually produced.              *)
(***************************************************************************)
EventualAmplification ==
    (InitPrimers > 0 /\ InitDS + InitSS > 0)
        => <>(Strands > 2 * InitDS + InitSS)

EventualNewDoubleStrand ==
    (InitPrimers > 0 /\ InitDS + InitSS > 0)
        => <>(ds > 0 /\ Strands > 2 * InitDS + InitSS)

(***************************************************************************)
(* Eventual depletion. Amplification stops only by running out of primers, *)
(* because templates are never lost. So once templates exist, every primer *)
(* is eventually incorporated into a strand.                               *)
(***************************************************************************)
EventualPrimerDepletion ==
    (InitDS + InitSS > 0) => <>[](primers = 0 /\ hybrid = 0)

\* Amplification is bounded by the primer supply.
AmplificationBounded ==
    [](Strands <= 2 * InitDS + InitSS + InitPrimers)

-----------------------------------------------------------------------------
THEOREM Spec => []SafetyInv
THEOREM Spec => InfiniteCycling
THEOREM Spec => EventualAmplification
THEOREM Spec => EventualPrimerDepletion
=============================================================================