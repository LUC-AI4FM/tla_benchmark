------------------------------- MODULE pcr_dna -------------------------------
(***************************************************************************)
(* High-resolution model of the Polymerase Chain Reaction (PCR).           *)
(*                                                                         *)
(* Species tracked:                                                        *)
(*   longLongDouble  : original double-stranded template DNA               *)
(*   shortLongDouble : long template strand + newly synthesized short one  *)
(*   tinyShortDouble : short template strand + newly synthesized tiny one  *)
(*   product         : tiny-tiny double strand (the defined PCR product)   *)
(*   longTemplate, shortTemplate, tinyTemplate : free single strands       *)
(*   longHybrid, shortHybrid, tinyHybrid       : primer-template hybrids   *)
(*   primer          : free primers                                        *)
(***************************************************************************)
EXTENDS Naturals

---------------------------- MODULE stages ----------------------------------
(***************************************************************************)
(* Coarse, staged abstraction of PCR.                                      *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS DNA, PRIMER

VARIABLES tee, primer, dna, template, hybrid, stage, cycle

svars == <<tee, primer, dna, template, hybrid, stage, cycle>>

natMin(a, b) == IF a < b THEN a ELSE b

TypeOK ==
    /\ tee \in {"Hot", "Warm", "TooHot"}
    /\ primer \in Nat
    /\ dna \in Nat
    /\ template \in Nat
    /\ hybrid \in Nat
    /\ stage \in {"init", "ready", "annealed", "extended", "denatured"}
    /\ cycle \in Nat

Init ==
    /\ tee = "Hot"
    /\ primer = PRIMER
    /\ dna = DNA
    /\ template = 0
    /\ hybrid = 0
    /\ stage = "init"
    /\ cycle = 0

heat ==
    /\ tee = "Hot"
    /\ tee' = "TooHot"
    /\ stage \in {"init", "extended"}
    /\ stage' = "denatured"
    /\ primer' = primer + hybrid
    /\ dna' = 0
    /\ template' = template + hybrid + 2 * dna
    /\ hybrid' = 0
    /\ UNCHANGED cycle

cool ==
    /\ tee = "TooHot"
    /\ tee' = "Hot"
    /\ stage = "denatured"
    /\ stage' = "ready"
    /\ UNCHANGED <<primer, dna, template, hybrid, cycle>>

anneal ==
    /\ tee = "Hot"
    /\ tee' = "Warm"
    /\ stage = "ready"
    /\ stage' = "annealed"
    /\ \E k \in 1..natMin(primer, template) :
          /\ primer' = primer - k
          /\ template' = template - k
          /\ hybrid' = hybrid + k
    /\ UNCHANGED <<dna, cycle>>

extend ==
    /\ tee = "Warm"
    /\ tee' = "Hot"
    /\ stage = "annealed"
    /\ stage' = "extended"
    /\ dna' = dna + hybrid
    /\ hybrid' = 0
    /\ cycle' = cycle + 1
    /\ UNCHANGED <<primer, template>>

Next == heat \/ cool \/ anneal \/ extend

Spec ==
    /\ Init
    /\ [][Next]_svars
    /\ WF_svars(heat)
    /\ WF_svars(cool)
    /\ WF_svars(anneal)
    /\ WF_svars(extend)

primerDepleted == <>(primer = 0)
=============================================================================