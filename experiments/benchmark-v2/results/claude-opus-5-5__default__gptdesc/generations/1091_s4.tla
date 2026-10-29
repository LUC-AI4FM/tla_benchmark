---------------------------- MODULE PCR ----------------------------
(***************************************************************************)
(* A very abstract model of the Polymerase Chain Reaction (PCR) cycle.    *)
(* It tracks the temperature and counts of primers, double-stranded DNA,  *)
(* single-stranded templates and template-primer hybrids.  Many           *)
(* biochemical details are omitted; PCR is treated as a coarse            *)
(* state-transition system.                                               *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS PRIMER   \* initial number of primers

ASSUME PRIMERAssumption == PRIMER \in Nat

VARIABLES tee,      \* temperature: "Hot" or "TooHot"
          primer,   \* number of free primers
          dna,      \* number of double-stranded DNA molecules
          template, \* number of single-stranded templates
          hybrid    \* number of template-primer hybrids

vars == <<tee, primer, dna, template, hybrid>>

natMin(i, j) == IF i < j THEN i ELSE j

(***************************************************************************)
(* Actions                                                                *)
(***************************************************************************)

\* Heating denatures: DNA splits into two templates, hybrids release their
\* primer and template.
heat == /\ tee = "Hot"
        /\ tee' = "TooHot"
        /\ primer' = primer + hybrid
        /\ template' = template + hybrid + 2 * dna
        /\ dna' = 0
        /\ hybrid' = 0

\* Cooling returns the mixture to the working temperature.
cool == /\ tee = "TooHot"
        /\ tee' = "Hot"
        /\ UNCHANGED <<primer, dna, template, hybrid>>

\* Annealing nondeterministically binds some number of primers to templates.
anneal == /\ tee = "Hot"
          /\ \E k \in 1..natMin(primer, template) :
                /\ primer' = primer - k
                /\ template' = template - k
                /\ hybrid' = hybrid + k
          /\ UNCHANGED <<tee, dna>>

\* Extension converts all hybrids into double-stranded DNA.
extend == /\ tee = "Hot"
          /\ dna' = dna + hybrid
          /\ hybrid' = 0
          /\ UNCHANGED <<tee, primer, template>>

(***************************************************************************)
(* Specification                                                          *)
(***************************************************************************)

Init == /\ tee = "Hot"
        /\ primer = PRIMER
        /\ dna = 1
        /\ template = 0
        /\ hybrid = 0

Next == heat \/ cool \/ anneal \/ extend

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Safety properties                                                      *)
(***************************************************************************)

TypeOK == /\ tee \in {"Hot", "TooHot"}
          /\ primer \in Nat
          /\ dna \in Nat
          /\ template \in Nat
          /\ hybrid \in Nat

NonNegative == /\ primer >= 0
               /\ dna >= 0
               /\ template >= 0
               /\ hybrid >= 0

\* Count preservation: each DNA/hybrid accounts for two strands.
PreservationInvariant ==
    template + primer + 2 * (dna + hybrid) = PRIMER + 2

(***************************************************************************)
(* Liveness property                                                      *)
(* NOTE: This property does NOT hold.  Weak fairness on Next only ensures *)
(* some step keeps happening; the system may cycle forever through heat   *)
(* and cool (or extend steps) without ever annealing, so primers need     *)
(* never be depleted.                                                     *)
(***************************************************************************)

EventuallyDepleted == <>(primer = 0)

THEOREM Spec => [](TypeOK /\ NonNegative /\ PreservationInvariant)
=============================================================================