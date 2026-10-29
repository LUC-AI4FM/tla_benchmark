------------------------------- MODULE PCR -------------------------------
(***************************************************************************)
(* A model of the Polymerase Chain Reaction (PCR) that tracks the full     *)
(* molecular inventory through repeated thermal cycles.                    *)
(*                                                                         *)
(* Single-stranded templates come in three lengths:                        *)
(*   ssLong  : original full-length strands                                *)
(*   ssMid   : intermediate strands (primer at one end only)               *)
(*   ssShort : exact-length strands (bounded by primers at both ends)      *)
(*                                                                         *)
(* A primer annealed to a template forms a hybrid.  Extension turns a      *)
(* hybrid into a double-stranded molecule:                                 *)
(*   long  template + primer --> dsLongMid   (intermediate generation)     *)
(*   mid   template + primer --> dsMidShort  (intermediate generation)     *)
(*   short template + primer --> dsShort     (exact-length PCR product)    *)
(* The original double-stranded DNA is dsFull (full-length generation).    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS DNA,      \* initial number of double-stranded DNA molecules
          PRIMER    \* initial number of free primers

ASSUME DNA \in Nat \ {0}
ASSUME PRIMER \in Nat

Stages == {"extended", "denatured", "cooled", "annealed"}

VARIABLES
    stage,        \* current temperature stage
    cycle,        \* number of completed cycles
    primer,       \* free primers
    ssLong, ssMid, ssShort,       \* single-stranded templates
    hyLong, hyMid, hyShort,       \* template/primer hybrids
    dsFull,                       \* full-length double strands
    dsLongMid, dsMidShort,        \* intermediate-length double strands
    dsShort                       \* exact-length double strands (product)

vars == << stage, cycle, primer,
           ssLong, ssMid, ssShort,
           hyLong, hyMid, hyShort,
           dsFull, dsLongMid, dsMidShort, dsShort >>

(* Three generations of double-stranded molecule *)
FullLengthDS   == dsFull
IntermediateDS == dsLongMid + dsMidShort
ShortDS        == dsShort

TypeOK ==
    /\ stage \in Stages
    /\ cycle \in Nat
    /\ primer \in Nat
    /\ ssLong \in Nat /\ ssMid \in Nat /\ ssShort \in Nat
    /\ hyLong \in Nat /\ hyMid \in Nat /\ hyShort \in Nat
    /\ dsFull \in Nat /\ dsLongMid \in Nat
    /\ dsMidShort \in Nat /\ dsShort \in Nat

Init ==
    /\ stage = "extended"      \* initial mixture behaves like post-extension
    /\ cycle = 0
    /\ primer = PRIMER
    /\ ssLong = 0 /\ ssMid = 0 /\ ssShort = 0
    /\ hyLong = 0 /\ hyMid = 0 /\ hyShort = 0
    /\ dsFull = DNA
    /\ dsLongMid = 0 /\ dsMidShort = 0 /\ dsShort = 0

(* Extreme heat: everything separates, free primers are recovered *)
Denature ==
    /\ stage = "extended"
    /\ stage' = "denatured"
    /\ ssLong'  = ssLong  + 2 * dsFull + dsLongMid + hyLong
    /\ ssMid'   = ssMid   + dsLongMid + dsMidShort + hyMid
    /\ ssShort' = ssShort + dsMidShort + 2 * dsShort + hyShort
    /\ primer'  = primer + hyLong + hyMid + hyShort
    /\ hyLong' = 0 /\ hyMid' = 0 /\ hyShort' = 0
    /\ dsFull' = 0 /\ dsLongMid' = 0 /\ dsMidShort' = 0 /\ dsShort' = 0
    /\ UNCHANGED cycle

(* Cooling in preparation for annealing *)
Cool ==
    /\ stage = "denatured"
    /\ stage' = "cooled"
    /\ UNCHANGED << cycle, primer, ssLong, ssMid, ssShort,
                    hyLong, hyMid, hyShort,
                    dsFull, dsLongMid, dsMidShort, dsShort >>

(* Warm: primers bind nondeterministically to available templates.       *)
(* If primers and templates are both available, at least one binds.      *)
Anneal ==
    /\ stage = "cooled"
    /\ stage' = "annealed"
    /\ \E kl \in 0..ssLong, km \in 0..ssMid, ks \in 0..ssShort :
          /\ kl + km + ks <= primer
          /\ (primer > 0 /\ ssLong + ssMid + ssShort > 0) => kl + km + ks > 0
          /\ primer'  = primer - (kl + km + ks)
          /\ ssLong'  = ssLong - kl
          /\ ssMid'   = ssMid - km
          /\ ssShort' = ssShort - ks
          /\ hyLong'  = hyLong + kl
          /\ hyMid'   = hyMid + km
          /\ hyShort' = hyShort + ks
    /\ UNCHANGED << cycle, dsFull, dsLongMid, dsMidShort, dsShort >>

(* Moderate heat: hybrids are extended into double-stranded molecules *)
Extend ==
    /\ stage = "annealed"
    /\ stage' = "extended"
    /\ dsLongMid'  = dsLongMid + hyLong
    /\ dsMidShort' = dsMidShort + hyMid
    /\ dsShort'    = dsShort + hyShort
    /\ hyLong' = 0 /\ hyMid' = 0 /\ hyShort' = 0
    /\ cycle' = cycle + 1
    /\ UNCHANGED << primer, ssLong, ssMid, ssShort, dsFull >>

Next == Denature \/ Cool \/ Anneal \/ Extend

Fairness ==
    /\ WF_vars(Denature)
    /\ WF_vars(Cool)
    /\ WF_vars(Anneal)
    /\ WF_vars(Extend)

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Safety *)

\* No exact-length product exists before three cycles have completed.
NoEarlyProduct == (cycle < 3) => (dsShort = 0 /\ hyShort = 0 /\ ssShort = 0)

\* Intermediate strands cannot exist before the first cycle completes.
NoEarlyIntermediate == (cycle < 1) => (ssMid = 0 /\ hyMid = 0 /\ IntermediateDS = 0)

\* Primers never exceed the initial supply.
PrimerBound == primer <= PRIMER

Inv == TypeOK /\ NoEarlyProduct /\ NoEarlyIntermediate /\ PrimerBound

(* Liveness *)

StageProgress ==
    /\ []<>(stage = "denatured")
    /\ []<>(stage = "cooled")
    /\ []<>(stage = "annealed")
    /\ []<>(stage = "extended")

PrimersDepleted == <>[](primer = 0)

---------------------------------------------------------------------------
(* Abstract specification: aggregate template, hybrid and total double-   *)
(* stranded counts through the same stage sequence.  It is stated over    *)
(* the refinement mapping below.                                          *)

aTemplates == ssLong + ssMid + ssShort
aHybrids   == hyLong + hyMid + hyShort
aDS        == dsFull + dsLongMid + dsMidShort + dsShort

absVars == << stage, aTemplates, aHybrids, aDS >>

AInit ==
    /\ stage = "extended"
    /\ aTemplates = 0
    /\ aHybrids = 0
    /\ aDS = DNA

ADenature ==
    /\ stage = "extended"
    /\ stage' = "denatured"
    /\ aTemplates' = aTemplates + 2 * aDS + aHybrids
    /\ aHybrids' = 0
    /\ aDS' = 0

ACool ==
    /\ stage = "denatured"
    /\ stage' = "cooled"
    /\ aTemplates' = aTemplates
    /\ aHybrids' = aHybrids
    /\ aDS' = aDS

AAnneal ==
    /\ stage = "cooled"
    /\ stage' = "annealed"
    /\ \E k \in 0..aTemplates :
          /\ aTemplates' = aTemplates - k
          /\ aHybrids' = aHybrids + k
    /\ aDS' = aDS

AExtend ==
    /\ stage = "annealed"
    /\ stage' = "extended"
    /\ aDS' = aDS + aHybrids
    /\ aHybrids' = 0
    /\ aTemplates' = aTemplates

ANext == ADenature \/ ACool \/ AAnneal \/ AExtend

AbsSpec ==
    /\ AInit
    /\ [][ANext]_absVars
    /\ WF_absVars(ADenature)
    /\ WF_absVars(ACool)
    /\ WF_absVars(AAnneal)
    /\ WF_absVars(AExtend)

---------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => StageProgress
THEOREM Spec => PrimersDepleted
THEOREM Spec => AbsSpec
===========================================================================