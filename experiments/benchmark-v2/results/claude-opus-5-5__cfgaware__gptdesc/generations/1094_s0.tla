---------------------------- MODULE stages ----------------------------
EXTENDS Naturals

CONSTANTS DNA, PRIMER

ASSUME DNA \in Nat /\ PRIMER \in Nat

VARIABLES tee, primer, dna, template, hybrid, stage, cycle

vars == <<tee, primer, dna, template, hybrid, stage, cycle>>

natMin(a, b) == IF a < b THEN a ELSE b

Temps  == {"Hot", "TooHot", "Warm"}
Stages == {"init", "heated", "cooled", "annealed", "extended"}

TypeOK ==
    /\ tee \in Temps
    /\ primer \in Nat
    /\ dna \in Nat
    /\ template \in Nat
    /\ hybrid \in Nat
    /\ stage \in Stages
    /\ cycle \in Nat

Init ==
    /\ tee = "Hot"
    /\ primer = PRIMER
    /\ dna = DNA
    /\ template = 0
    /\ hybrid = 0
    /\ stage = "init"
    /\ cycle = 0

(* Denaturation: heat separates double-stranded DNA into single strands *)
heat ==
    /\ stage \in {"init", "extended"}
    /\ tee = "Hot"
    /\ tee' = "TooHot"
    /\ template' = template + 2 * dna
    /\ dna' = 0
    /\ stage' = "heated"
    /\ UNCHANGED <<primer, hybrid, cycle>>

(* Cooling back down before annealing *)
cool ==
    /\ stage = "heated"
    /\ tee = "TooHot"
    /\ tee' = "Hot"
    /\ stage' = "cooled"
    /\ UNCHANGED <<primer, dna, template, hybrid, cycle>>

(* Annealing: primers bind to single-stranded templates *)
anneal ==
    /\ stage = "cooled"
    /\ tee = "Hot"
    /\ LET k == natMin(template, primer)
       IN /\ hybrid' = hybrid + k
          /\ template' = template - k
          /\ primer' = primer - k
    /\ tee' = "Warm"
    /\ stage' = "annealed"
    /\ UNCHANGED <<dna, cycle>>

(* Extension: hybrids are extended into double-stranded DNA *)
extend ==
    /\ stage = "annealed"
    /\ tee = "Warm"
    /\ dna' = dna + hybrid
    /\ hybrid' = 0
    /\ tee' = "Hot"
    /\ stage' = "extended"
    /\ cycle' = IF hybrid > 0 THEN cycle + 1 ELSE cycle
    /\ UNCHANGED <<primer, template>>

Next == heat \/ cool \/ anneal \/ extend

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(heat)
    /\ WF_vars(cool)
    /\ WF_vars(anneal)
    /\ WF_vars(extend)

-----------------------------------------------------------------------------
(* Clean (abstract) model, expressed through a refinement mapping *)

cTee == IF tee = "TooHot" THEN "TooHot" ELSE "Hot"
cDna == 2 * dna + template + 2 * hybrid

cVars == <<cTee, primer, cDna>>

cInit ==
    /\ cTee = "Hot"
    /\ primer = PRIMER
    /\ cDna = 2 * DNA

cHeat ==
    /\ cTee = "Hot"
    /\ cTee' = "TooHot"
    /\ primer' = primer
    /\ cDna' = cDna

cCool ==
    /\ cTee = "TooHot"
    /\ cTee' = "Hot"
    /\ primer' = primer
    /\ cDna' = cDna

cAnneal ==
    /\ cTee = "Hot"
    /\ cTee' = cTee
    /\ \E k \in 1..primer :
         /\ primer' = primer - k
         /\ cDna' = cDna + k

cNext == cHeat \/ cCool \/ cAnneal

cleanSpec == cInit /\ [][cNext]_cVars

primerDepleted == <>(primer = 0)

=============================================================================