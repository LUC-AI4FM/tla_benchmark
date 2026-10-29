---------------------------- MODULE PCR ----------------------------
(***************************************************************************)
(* A very abstract model of the Polymerase Chain Reaction (PCR) cycle.     *)
(*                                                                         *)
(* The state tracks the temperature of the reaction and the number of:    *)
(*   primer   - free primers                                               *)
(*   dna      - double-stranded DNA molecules                              *)
(*   template - single-stranded templates                                  *)
(*   hybrid   - template-primer hybrids                                    *)
(*                                                                         *)
(* The cycle works as follows:                                             *)
(*   heat   - denaturation: dna and hybrids separate into single strands.  *)
(*   cool   - the mixture cools down from denaturation temperature.        *)
(*   anneal - primers bind to templates, forming hybrids. Some             *)
(*            nondeterministic number of primers and templates is used.    *)
(*   extend - the polymerase extends each hybrid into a full dna molecule. *)
(*                                                                         *)
(* Many biochemical details (nucleotides, polymerase, kinetics, etc.)     *)
(* are omitted on purpose: PCR is treated as a coarse transition system.   *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS PRIMER,   \* initial number of primers
          DNA       \* initial number of double-stranded DNA molecules

ASSUME /\ PRIMER \in Nat
       /\ DNA \in Nat

VARIABLES tee,      \* temperature of the reaction
          primer,   \* number of free primers
          dna,      \* number of double-stranded DNA molecules
          template, \* number of single-stranded templates
          hybrid    \* number of template-primer hybrids

vars == <<tee, primer, dna, template, hybrid>>

Temperatures == {"Hot", "TooHot", "Warm"}

Min(a, b) == IF a < b THEN a ELSE b

-----------------------------------------------------------------------------

Init == /\ tee = "Hot"
        /\ primer = PRIMER
        /\ dna = DNA
        /\ template = 0
        /\ hybrid = 0

(* Denaturation: double strands and hybrids melt into single strands.      *)
heat == /\ tee \in {"Hot", "Warm"}
        /\ tee' = "TooHot"
        /\ primer' = primer + hybrid
        /\ template' = template + hybrid + 2 * dna
        /\ dna' = 0
        /\ hybrid' = 0

(* The mixture cools down after denaturation.                              *)
cool == /\ tee = "TooHot"
        /\ tee' = "Hot"
        /\ UNCHANGED <<primer, dna, template, hybrid>>

(* Annealing: some number k of primers bind to k templates.                *)
anneal == /\ tee = "Hot"
          /\ tee' = "Warm"
          /\ \E k \in 1..Min(primer, template) :
                /\ primer' = primer - k
                /\ template' = template - k
                /\ hybrid' = hybrid + k
          /\ UNCHANGED dna

(* Extension: every hybrid is extended into a double-stranded DNA.         *)
extend == /\ tee = "Warm"
          /\ tee' = "Hot"
          /\ dna' = dna + hybrid
          /\ hybrid' = 0
          /\ UNCHANGED <<primer, template>>

Next == heat \/ cool \/ anneal \/ extend

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(Next)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

TypeOK == /\ tee \in Temperatures
          /\ primer \in Nat
          /\ dna \in Nat
          /\ template \in Nat
          /\ hybrid \in Nat

NonNegative == /\ primer >= 0
               /\ dna >= 0
               /\ template >= 0
               /\ hybrid >= 0

(* Count preservation: each dna and each hybrid accounts for two strands,  *)
(* each free primer and each template accounts for one strand.             *)
Preservation == primer + 2 * dna + template + 2 * hybrid = PRIMER + 2 * DNA

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness property                                                       *)
(*                                                                         *)
(* Claims that the primers are eventually all used up. NOTE: this does     *)
(* NOT hold. The system may, e.g., loop forever between heat and cool (or  *)
(* anneal only part of the primers each cycle), and weak fairness on Next  *)
(* does not force any annealing to occur.                                  *)
(***************************************************************************)
primerDepleted == <>(primer = 0)

THEOREM Spec => [](TypeOK /\ NonNegative /\ Preservation)

=============================================================================