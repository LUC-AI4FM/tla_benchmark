---------------------------- MODULE PCR ----------------------------
EXTENDS Naturals

CONSTANTS DNA,      \* initial stock of double-stranded DNA
          PRIMER    \* initial stock of primers

ASSUME DNA \in Nat /\ PRIMER \in Nat

VARIABLES tee,       \* current temperature state
          primer,    \* free primers
          dna,       \* double-stranded DNA
          template,  \* single-stranded templates
          hybrid     \* template-primer hybrids

vars == <<tee, primer, dna, template, hybrid>>

Temps == {"Moderate", "Hot", "Cool", "Warm"}

Min(a, b) == IF a < b THEN a ELSE b

TypeOK ==
    /\ tee \in Temps
    /\ primer \in Nat
    /\ dna \in Nat
    /\ template \in Nat
    /\ hybrid \in Nat

Init ==
    /\ tee = "Moderate"
    /\ primer = PRIMER
    /\ dna = DNA
    /\ template = 0
    /\ hybrid = 0

(* High heat: double-stranded DNA and hybrids denature.
   Each DNA yields two templates; each hybrid yields one template
   and one recovered free primer. *)
Heat ==
    /\ tee = "Moderate"
    /\ tee' = "Hot"
    /\ template' = template + hybrid + 2 * dna
    /\ primer' = primer + hybrid
    /\ dna' = 0
    /\ hybrid' = 0

(* Cooling: return to a state ready for annealing. *)
Cool ==
    /\ tee = "Hot"
    /\ tee' = "Cool"
    /\ UNCHANGED <<primer, dna, template, hybrid>>

(* Warm: a nondeterministic number of primers anneal to templates. *)
Anneal ==
    /\ tee = "Cool"
    /\ tee' = "Warm"
    /\ \E k \in 0..Min(primer, template) :
          /\ primer' = primer - k
          /\ template' = template - k
          /\ hybrid' = hybrid + k
    /\ UNCHANGED dna

(* Medium heat: polymerase extends all hybrids into new double-stranded DNA. *)
Extend ==
    /\ tee = "Warm"
    /\ tee' = "Moderate"
    /\ dna' = dna + hybrid
    /\ hybrid' = 0
    /\ UNCHANGED <<primer, template>>

Next == Heat \/ Cool \/ Anneal \/ Extend

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Conservation of weighted strand count *)

Total == primer + template + 2 * dna + 2 * hybrid

ConservationInv == Total = PRIMER + 2 * DNA

(* Stuttering-tolerant temporal form of the preservation property *)
Preservation == [][Total' = Total]_vars

PreservationProperty == []ConservationInv /\ Preservation

THEOREM Spec => []TypeOK
THEOREM Spec => []ConservationInv
THEOREM Spec => Preservation
=============================================================================