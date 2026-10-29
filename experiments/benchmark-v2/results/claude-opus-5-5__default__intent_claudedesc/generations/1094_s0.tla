------------------------------- MODULE stages -------------------------------
(***************************************************************************)
(* Stage-constrained model of the Polymerase Chain Reaction (PCR).        *)
(*                                                                         *)
(* Quantities tracked:                                                     *)
(*   dna      - number of double-stranded DNA molecules                    *)
(*   template - number of single-stranded templates                        *)
(*   hybrid   - number of primer-template hybrids                          *)
(*   primer   - number of free primers                                     *)
(*   tee      - current temperature                                        *)
(*   stage    - the thermal phase that was last completed                  *)
(*   cycle    - number of completed extension cycles                       *)
(*                                                                         *)
(* The stage variable allows only the next meaningful thermal step:        *)
(*   init/extended --heat--> heated --cool--> ready                        *)
(*   ready --anneal--> annealed --extend--> extended                       *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS DNA, PRIMER

ASSUME /\ DNA \in Nat \ {0}
       /\ PRIMER \in Nat

VARIABLES tee, primer, dna, template, hybrid, stage, cycle

vars == <<tee, primer, dna, template, hybrid, stage, cycle>>

Temperatures == {"Hot", "Warm", "TooHot"}
Stages       == {"init", "heated", "ready", "annealed", "extended"}

natMin(i, j) == IF i < j THEN i ELSE j

-----------------------------------------------------------------------------
(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK ==
    /\ tee      \in Temperatures
    /\ primer   \in Nat
    /\ dna      \in Nat
    /\ template \in Nat
    /\ hybrid   \in Nat
    /\ stage    \in Stages
    /\ cycle    \in Nat

-----------------------------------------------------------------------------
(***************************************************************************)
(* Initial state: a stock of double-stranded DNA and primers.             *)
(***************************************************************************)
Init ==
    /\ tee      = "Hot"
    /\ primer   = PRIMER
    /\ dna      = DNA
    /\ template = 0
    /\ hybrid   = 0
    /\ stage    = "init"
    /\ cycle    = 0

(***************************************************************************)
(* Denaturation: heating separates double strands into templates and      *)
(* releases primers from any remaining hybrids.                           *)
(***************************************************************************)
heat ==
    /\ stage \in {"init", "extended"}
    /\ tee = "Hot"
    /\ tee'      = "TooHot"
    /\ primer'   = primer + hybrid
    /\ dna'      = 0
    /\ template' = template + hybrid + 2 * dna
    /\ hybrid'   = 0
    /\ stage'    = "heated"
    /\ UNCHANGED cycle

(***************************************************************************)
(* Cooling to a ready state.                                               *)
(***************************************************************************)
cool ==
    /\ stage = "heated"
    /\ tee = "TooHot"
    /\ tee'   = "Hot"
    /\ stage' = "ready"
    /\ UNCHANGED <<primer, dna, template, hybrid, cycle>>

(***************************************************************************)
(* Annealing: primers bind to templates at a warm temperature.            *)
(***************************************************************************)
anneal ==
    /\ stage = "ready"
    /\ tee = "Hot"
    /\ tee'   = "Warm"
    /\ \E k \in 1..natMin(primer, template) :
          /\ primer'   = primer - k
          /\ template' = template - k
          /\ hybrid'   = hybrid + k
    /\ stage' = "annealed"
    /\ UNCHANGED <<dna, cycle>>

(***************************************************************************)
(* Extension: hybrids become new double strands at a hot temperature.     *)
(***************************************************************************)
extend ==
    /\ stage = "annealed"
    /\ tee = "Warm"
    /\ tee'    = "Hot"
    /\ dna'    = dna + hybrid
    /\ hybrid' = 0
    /\ cycle'  = cycle + 1
    /\ stage'  = "extended"
    /\ UNCHANGED <<primer, template>>

Next == heat \/ cool \/ anneal \/ extend

Fairness ==
    /\ WF_vars(heat)
    /\ WF_vars(cool)
    /\ WF_vars(anneal)
    /\ WF_vars(extend)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)

\* Primers are eventually depleted.
PrimersDepleted == <>(primer = 0)

\* As long as primers and templates (or material yielding templates)
\* remain available, the process keeps completing new cycles.
ContinuesCycling ==
    \A n \in 0..PRIMER :
        (cycle = n /\ primer > 0 /\ template + dna + hybrid > 0)
            ~> (cycle > n)

Liveness == PrimersDepleted /\ ContinuesCycling

THEOREM Spec => []TypeOK
THEOREM Spec => Liveness

-----------------------------------------------------------------------------
(***************************************************************************)
(* The previously established clean-PCR specification (no stage or cycle *)
(* bookkeeping; transitions guarded only by temperature).                 *)
(***************************************************************************)
cleanVars == <<tee, primer, dna, template, hybrid>>

CleanInit ==
    /\ tee      = "Hot"
    /\ primer   = PRIMER
    /\ dna      = DNA
    /\ template = 0
    /\ hybrid   = 0

CleanHeat ==
    /\ tee = "Hot"
    /\ tee'      = "TooHot"
    /\ primer'   = primer + hybrid
    /\ dna'      = 0
    /\ template' = template + hybrid + 2 * dna
    /\ hybrid'   = 0

CleanCool ==
    /\ tee = "TooHot"
    /\ tee' = "Hot"
    /\ UNCHANGED <<primer, dna, template, hybrid>>

CleanAnneal ==
    /\ tee = "Hot"
    /\ tee' = "Warm"
    /\ UNCHANGED dna
    /\ \E k \in 1..natMin(primer, template) :
          /\ primer'   = primer - k
          /\ template' = template - k
          /\ hybrid'   = hybrid + k

CleanExtend ==
    /\ tee = "Warm"
    /\ tee'    = "Hot"
    /\ dna'    = dna + hybrid
    /\ hybrid' = 0
    /\ UNCHANGED <<primer, template>>

CleanNext == CleanHeat \/ CleanCool \/ CleanAnneal \/ CleanExtend

CleanSpec == CleanInit /\ [][CleanNext]_cleanVars

\* Refinement property: the stage-constrained model implements clean PCR.
RefinesClean == CleanSpec

THEOREM Spec => RefinesClean

=============================================================================