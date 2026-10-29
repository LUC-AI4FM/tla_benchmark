---------------------------- MODULE pcr ----------------------------
(***************************************************************************)
(* A very abstract model of the PCR (polymerase chain reaction) cycle.    *)
(*                                                                         *)
(* The state tracks the temperature of the reaction mixture together with *)
(* counts of:                                                              *)
(*   - primer   : free primers                                             *)
(*   - dna      : double-stranded DNA molecules                            *)
(*   - template : single-stranded templates                                *)
(*   - hybrid   : template-primer hybrids                                  *)
(*                                                                         *)
(* The system moves through heating (denaturation), cooling, annealing,   *)
(* and extension.  Annealing nondeterministically binds some number of    *)
(* available primers to templates.  Extension turns hybrids into          *)
(* double-stranded DNA.                                                    *)
(*                                                                         *)
(* Many biochemical details are deliberately left out.  PCR is treated    *)
(* as a coarse state-transition system.                                    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS DNA,      \* initial number of double-stranded DNA molecules
          PRIMER    \* initial number of primers

ASSUME DNA \in Nat /\ PRIMER \in Nat

VARIABLES tee,      \* temperature
          primer,   \* number of free primers
          dna,      \* number of double-stranded DNA molecules
          template, \* number of single-stranded templates
          hybrid    \* number of template-primer hybrids

vars == <<tee, primer, dna, template, hybrid>>

Temps == {"Hot", "Cool", "Warm"}

natMin(i, j) == IF i < j THEN i ELSE j

TypeOK ==
    /\ tee \in Temps
    /\ primer \in Nat
    /\ dna \in Nat
    /\ template \in Nat
    /\ hybrid \in Nat

Init ==
    /\ tee = "Hot"
    /\ primer = PRIMER
    /\ dna = DNA
    /\ template = 0
    /\ hybrid = 0

(* Heating denatures everything into single strands.  Each DNA molecule  *)
(* yields two templates.  Each hybrid yields a template and releases its *)
(* primer.                                                                *)
heat ==
    /\ tee # "Hot"
    /\ tee' = "Hot"
    /\ primer' = primer + hybrid
    /\ dna' = 0
    /\ template' = template + hybrid + 2 * dna
    /\ hybrid' = 0

(* Cooling the mixture after denaturation. *)
cool ==
    /\ tee = "Hot"
    /\ tee' = "Cool"
    /\ UNCHANGED <<primer, dna, template, hybrid>>

(* Annealing binds some number k of primers to templates. *)
anneal ==
    /\ tee = "Cool"
    /\ tee' = "Warm"
    /\ \E k \in 0..natMin(primer, template) :
          /\ primer' = primer - k
          /\ template' = template - k
          /\ hybrid' = hybrid + k
    /\ UNCHANGED dna

(* Extension turns every hybrid into a double-stranded DNA molecule. *)
extend ==
    /\ tee = "Warm"
    /\ hybrid > 0
    /\ dna' = dna + hybrid
    /\ hybrid' = 0
    /\ UNCHANGED <<tee, primer, template>>

Next == heat \/ cool \/ anneal \/ extend

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety properties *)

primerPositive == primer >= 0

(* Count preservation.  Every strand is counted once.  A DNA molecule has  *)
(* two strands.  A hybrid has a template and a primer.  Free primers and  *)
(* templates count one each.                                               *)
preservationInvariant ==
    primer + 2 * dna + template + 2 * hybrid = PRIMER + 2 * DNA

(* Liveness: primers are eventually used up.  This does NOT hold.         *)
(* Annealing may bind zero primers.  Heating also returns primers from    *)
(* hybrids.  So the system can cycle forever without depleting primers.   *)
preservationProperty == <>(primer = 0)

=============================================================================