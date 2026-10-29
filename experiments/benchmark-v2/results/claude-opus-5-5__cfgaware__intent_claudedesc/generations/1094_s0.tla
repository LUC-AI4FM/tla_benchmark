------------------------------ MODULE pcr_stage ------------------------------
EXTENDS Naturals

CONSTANTS DNA, PRIMER

ASSUME DNA \in Nat /\ PRIMER \in Nat

VARIABLES tee, primer, dna, template, hybrid, stage, cycle

vars == << tee, primer, dna, template, hybrid, stage, cycle >>

cleanVars == << tee, primer, dna, template, hybrid >>

natMin(a, b) == IF a < b THEN a ELSE b

Temps  == {"TooHot", "Hot", "Warm"}
Stages == {"init", "denatured", "ready", "annealed", "extended"}

TypeOK ==
    /\ tee \in Temps
    /\ primer \in Nat
    /\ dna \in Nat
    /\ template \in Nat
    /\ hybrid \in Nat
    /\ stage \in Stages
    /\ cycle \in Nat

(***************************************************************************)
(* Clean PCR specification                                                 *)
(***************************************************************************)

cleanInit ==
    /\ tee = "Hot"
    /\ primer = PRIMER
    /\ dna = DNA
    /\ template = 0
    /\ hybrid = 0

cleanHeat ==
    /\ tee \in {"Hot", "Warm"}
    /\ tee' = "TooHot"
    /\ primer' = primer + hybrid
    /\ dna' = 0
    /\ template' = template + hybrid + 2 * dna
    /\ hybrid' = 0

cleanCool ==
    /\ tee = "TooHot"
    /\ tee' = "Hot"
    /\ UNCHANGED << primer, dna, template, hybrid >>

cleanAnneal ==
    /\ tee = "Hot"
    /\ tee' = "Warm"
    /\ UNCHANGED dna
    /\ \E k \in 1..natMin(primer, template) :
          /\ primer' = primer - k
          /\ template' = template - k
          /\ hybrid' = hybrid + k

cleanExtend ==
    /\ tee = "Warm"
    /\ tee' = "Hot"
    /\ UNCHANGED << primer, template >>
    /\ dna' = dna + hybrid
    /\ hybrid' = 0

cleanNext == cleanHeat \/ cleanCool \/ cleanAnneal \/ cleanExtend

cleanSpec ==
    /\ cleanInit
    /\ [][cleanNext]_cleanVars
    /\ WF_cleanVars(cleanHeat)
    /\ WF_cleanVars(cleanCool)
    /\ WF_cleanVars(cleanAnneal)
    /\ WF_cleanVars(cleanExtend)

(***************************************************************************)
(* Stage-constrained PCR specification                                     *)
(***************************************************************************)

CanAnneal == natMin(primer, template) > 0

Init ==
    /\ tee = "Hot"
    /\ primer = PRIMER
    /\ dna = DNA
    /\ template = 0
    /\ hybrid = 0
    /\ stage = "init"
    /\ cycle = 0

(* Denaturation: allowed at the start, after an extension, or when ready  *)
(* but no annealing is possible any more.                                  *)
heat ==
    /\ \/ stage \in {"init", "extended"}
       \/ stage = "ready" /\ ~CanAnneal
    /\ tee \in {"Hot", "Warm"}
    /\ tee' = "TooHot"
    /\ primer' = primer + hybrid
    /\ dna' = 0
    /\ template' = template + hybrid + 2 * dna
    /\ hybrid' = 0
    /\ stage' = "denatured"
    /\ UNCHANGED cycle

cool ==
    /\ stage = "denatured"
    /\ tee = "TooHot"
    /\ tee' = "Hot"
    /\ stage' = "ready"
    /\ UNCHANGED << primer, dna, template, hybrid, cycle >>

anneal ==
    /\ stage = "ready"
    /\ tee = "Hot"
    /\ tee' = "Warm"
    /\ UNCHANGED << dna, cycle >>
    /\ \E k \in 1..natMin(primer, template) :
          /\ primer' = primer - k
          /\ template' = template - k
          /\ hybrid' = hybrid + k
    /\ stage' = "annealed"

extend ==
    /\ stage = "annealed"
    /\ tee = "Warm"
    /\ tee' = "Hot"
    /\ UNCHANGED << primer, template >>
    /\ dna' = dna + hybrid
    /\ hybrid' = 0
    /\ stage' = "extended"
    /\ cycle' = cycle + 1

Next == heat \/ cool \/ anneal \/ extend

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(heat)
    /\ WF_vars(cool)
    /\ WF_vars(anneal)
    /\ WF_vars(extend)

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

primerDepleted == <>(primer = 0)

KeepsCycling ==
    [](stage = "ready" /\ CanAnneal => <>(stage = "extended"))

=============================================================================