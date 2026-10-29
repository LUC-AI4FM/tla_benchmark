------------------------------- MODULE stages -------------------------------
EXTENDS Naturals

CONSTANTS DNA,      \* initial stock of double-stranded DNA
          PRIMER    \* initial stock of primers

VARIABLES tee,       \* temperature
          primer,    \* free primers
          dna,       \* double-stranded DNA
          template,  \* single-stranded templates
          hybrid,    \* primer/template hybrids
          stage,     \* current stage of the PCR cycle
          cycle      \* number of completed cycles

vars      == <<tee, primer, dna, template, hybrid, stage, cycle>>
cleanVars == <<tee, primer, dna, template, hybrid>>

natMin(i, j) == IF i < j THEN i ELSE j

-----------------------------------------------------------------------------
(* The underlying "clean" specification (without stages/cycles).           *)

cleanInit == /\ tee = "Hot"
             /\ primer = PRIMER
             /\ dna = DNA
             /\ template = 0
             /\ hybrid = 0

cleanHeat == /\ tee = "Hot"
             /\ tee' = "TooHot"
             /\ primer' = primer + hybrid
             /\ dna' = 0
             /\ template' = template + hybrid + 2 * dna
             /\ hybrid' = 0

cleanCool == /\ tee = "TooHot"
             /\ tee' = "Hot"
             /\ UNCHANGED <<primer, dna, template, hybrid>>

cleanAnneal == /\ tee = "Hot"
               /\ tee' = "Warm"
               /\ UNCHANGED dna
               /\ \E k \in 1..natMin(primer, template) :
                     /\ primer' = primer - k
                     /\ template' = template - k
                     /\ hybrid' = hybrid + k

cleanExtend == /\ tee = "Warm"
               /\ tee' = "Hot"
               /\ UNCHANGED <<primer, template>>
               /\ dna' = dna + hybrid
               /\ hybrid' = 0

cleanNext == cleanHeat \/ cleanCool \/ cleanAnneal \/ cleanExtend

cleanSpec == cleanInit /\ [][cleanNext]_cleanVars

primerDepleted == <>(primer = 0)

-----------------------------------------------------------------------------
(* The staged specification.                                                *)

TypeOK == /\ tee \in {"Warm", "Hot", "TooHot"}
          /\ primer \in Nat
          /\ dna \in Nat
          /\ template \in Nat
          /\ hybrid \in Nat
          /\ stage \in {"init", "denatured", "ready", "annealed", "extended"}
          /\ cycle \in Nat

Init == /\ tee = "Hot"
        /\ primer = PRIMER
        /\ dna = DNA
        /\ template = 0
        /\ hybrid = 0
        /\ stage = "init"
        /\ cycle = 0

heat == /\ tee = "Hot"
        /\ stage \in {"init", "extended"}
        /\ tee' = "TooHot"
        /\ primer' = primer + hybrid
        /\ dna' = 0
        /\ template' = template + hybrid + 2 * dna
        /\ hybrid' = 0
        /\ stage' = "denatured"
        /\ UNCHANGED cycle

cool == /\ stage = "denatured"
        /\ tee = "TooHot"
        /\ tee' = "Hot"
        /\ stage' = "ready"
        /\ UNCHANGED <<primer, dna, template, hybrid, cycle>>

anneal == /\ stage = "ready"
          /\ tee = "Hot"
          /\ tee' = "Warm"
          /\ UNCHANGED <<dna, cycle>>
          /\ \E k \in 1..natMin(primer, template) :
                /\ primer' = primer - k
                /\ template' = template - k
                /\ hybrid' = hybrid + k
          /\ stage' = "annealed"

extend == /\ stage = "annealed"
          /\ tee = "Warm"
          /\ tee' = "Hot"
          /\ UNCHANGED <<primer, template>>
          /\ dna' = dna + hybrid
          /\ hybrid' = 0
          /\ cycle' = cycle + 1
          /\ stage' = "extended"

Next == heat \/ cool \/ anneal \/ extend

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(heat)
        /\ WF_vars(cool)
        /\ WF_vars(anneal)
        /\ WF_vars(extend)

=============================================================================