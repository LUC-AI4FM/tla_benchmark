------------------------------- MODULE pcr -------------------------------
(***************************************************************************)
(* An abstract model of DNA amplification (PCR).                           *)
(*                                                                         *)
(* The thermal cycle has these phases:                                     *)
(*   "TooHot" : denaturation. All double strands melt into single strands. *)
(*   "Hot"    : the mixture has cooled. Primers may now anneal.            *)
(*   "Warm"   : primers have annealed to templates. Polymerase extends     *)
(*              each primer-template hybrid into double-stranded DNA.      *)
(*                                                                         *)
(* The variables count molecular species:                                  *)
(*   primer   : free single-stranded primers                               *)
(*   template : free single-stranded template strands                      *)
(*   hybrid   : primer-template complexes (2 strands each)                 *)
(*   dna      : double-stranded DNA molecules (2 strands each)             *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS DNA,      \* initial amount of double-stranded target DNA
          PRIMER    \* initial amount of primers

ASSUME /\ DNA \in Nat
       /\ PRIMER \in Nat

VARIABLES tee,       \* current temperature phase
          primer,
          dna,
          template,
          hybrid

vars == << tee, primer, dna, template, hybrid >>

Phases == {"TooHot", "Hot", "Warm"}

Min(a, b) == IF a < b THEN a ELSE b

-----------------------------------------------------------------------------

Init == /\ tee = "Hot"
        /\ primer = PRIMER
        /\ dna = DNA
        /\ template = 0
        /\ hybrid = 0

(* Denaturation: each DNA molecule becomes two templates, and each hybrid  *)
(* becomes one primer and one template.                                    *)
heat == /\ tee \in {"Hot", "Warm"}
        /\ tee' = "TooHot"
        /\ primer' = primer + hybrid
        /\ template' = template + hybrid + 2 * dna
        /\ dna' = 0
        /\ hybrid' = 0

(* The mixture cools after denaturation, making annealing possible.       *)
cool == /\ tee = "TooHot"
        /\ tee' = "Hot"
        /\ UNCHANGED << primer, dna, template, hybrid >>

(* Annealing: some number k of primers bind to k templates.               *)
anneal == /\ tee = "Hot"
          /\ tee' = "Warm"
          /\ \E k \in 1..Min(primer, template) :
                /\ primer' = primer - k
                /\ template' = template - k
                /\ hybrid' = hybrid + k
          /\ UNCHANGED dna

(* Extension: every primer-template hybrid is extended into a full DNA     *)
(* double strand.                                                          *)
extend == /\ tee = "Warm"
          /\ tee' = "Hot"
          /\ dna' = dna + hybrid
          /\ hybrid' = 0
          /\ UNCHANGED << primer, template >>

Next == heat \/ cool \/ anneal \/ extend

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Properties                                                              *)

TypeOK == /\ tee \in Phases
          /\ primer \in Nat
          /\ dna \in Nat
          /\ template \in Nat
          /\ hybrid \in Nat

(* Conservation of mass: counting single strands, a primer and a template *)
(* count once, while hybrids and DNA molecules each count twice.          *)
preservationInvariant ==
    template + primer + 2 * (dna + hybrid) = PRIMER + 2 * DNA

(* Primers are not yet exhausted.                                          *)
primerPositive == primer > 0

(* Proper sequencing of the thermal phases.                                *)
PhaseOrder ==
    [][ \/ tee = "TooHot" /\ tee' = "Hot"
        \/ tee = "Hot"    /\ tee' \in {"Warm", "TooHot"}
        \/ tee = "Warm"   /\ tee' \in {"Hot", "TooHot"} ]_tee

(* Amplification never loses DNA strands between extension steps.         *)
DnaGrowsOnExtend == [][extend => dna' >= dna]_vars

=============================================================================