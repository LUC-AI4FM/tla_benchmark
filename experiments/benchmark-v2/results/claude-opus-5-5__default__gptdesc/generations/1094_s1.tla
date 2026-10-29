------------------------------- MODULE stages -------------------------------
(***************************************************************************)
(* A simplified PCR (polymerase chain reaction) process with explicit     *)
(* thermal stages and molecular counts.                                   *)
(*                                                                         *)
(*   tee      : temperature of the thermocycler ("Hot" or "Cold")         *)
(*   primer   : number of free primers remaining                          *)
(*   dna      : number of double-stranded DNA molecules                   *)
(*   template : number of single-stranded template strands                *)
(*   hybrid   : number of template-primer hybrids                         *)
(*   stage    : stage/history variable that orders the actions            *)
(*   cycle    : number of completed PCR cycles                            *)
(*                                                                         *)
(* The stage variable forces heat -> cool -> anneal -> extend -> heat ... *)
(* This module refines the unconstrained "clean" model, defined below and *)
(* instantiated after the declarations. Its properties are imported here. *)
(***************************************************************************)
EXTENDS Naturals

-------------------------------- MODULE clean --------------------------------
(***************************************************************************)
(* The "clean" PCR model: the same molecular actions, with no ordering    *)
(* imposed by a stage variable.                                           *)
(***************************************************************************)
CONSTANTS DNA, PRIMER

VARIABLES tee, primer, dna, template, hybrid

cvars == << tee, primer, dna, template, hybrid >>

CMin(a, b) == IF a < b THEN a ELSE b

TypeOK ==
    /\ tee \in {"Hot", "Cold"}
    /\ primer \in Nat
    /\ dna \in Nat
    /\ template \in Nat
    /\ hybrid \in Nat

Init ==
    /\ tee = "Cold"
    /\ primer = PRIMER
    /\ dna = DNA
    /\ template = 0
    /\ hybrid = 0

(* Heating denatures double strands and separates hybrids. *)
Heat ==
    /\ tee = "Cold"
    /\ tee' = "Hot"
    /\ template' = template + hybrid + 2 * dna
    /\ primer' = primer + hybrid
    /\ dna' = 0
    /\ hybrid' = 0

Cool ==
    /\ tee = "Hot"
    /\ tee' = "Cold"
    /\ UNCHANGED << primer, dna, template, hybrid >>

(* Some primers bind to single-stranded templates. *)
Anneal ==
    /\ tee = "Cold"
    /\ \E k \in 1..CMin(primer, template) :
         /\ primer' = primer - k
         /\ template' = template - k
         /\ hybrid' = hybrid + k
    /\ UNCHANGED << tee, dna >>

(* Polymerase extends every hybrid into a double-stranded molecule. *)
Extend ==
    /\ tee = "Cold"
    /\ hybrid > 0
    /\ dna' = dna + hybrid
    /\ hybrid' = 0
    /\ UNCHANGED << tee, primer, template >>

Next == Heat \/ Cool \/ Anneal \/ Extend

Spec == Init /\ [][Next]_cvars

(* Strand conservation: every new strand consumed exactly one primer. *)
Conservation ==
    template + 2 * hybrid + 2 * dna = 2 * DNA + PRIMER - primer

(* Eventually all primers are consumed. *)
primerDepleted == <>(primer = 0)
==============================================================================