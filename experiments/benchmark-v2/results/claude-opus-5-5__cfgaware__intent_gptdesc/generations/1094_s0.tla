---------------------------- MODULE PCR ----------------------------
(***************************************************************************)
(* A model of the polymerase chain reaction (PCR): a cyclic biochemical    *)
(* amplification process alternating temperature-controlled phases.        *)
(*                                                                         *)
(*   dna      - number of double-stranded templates                        *)
(*   template - number of single-stranded templates                        *)
(*   primer   - number of free primers                                     *)
(*   hybrid   - number of primer-template hybrids                          *)
(*   tee      - discrete temperature mode                                  *)
(*   cycle    - number of completed amplification (extension) cycles       *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS DNA,     \* initial number of double-stranded templates
          PRIMER   \* initial (finite) supply of primers

ASSUME DNA \in Nat /\ PRIMER \in Nat

VARIABLES tee, primer, dna, template, hybrid, cycle

vars == <<tee, primer, dna, template, hybrid, cycle>>

Temps == {"Hot", "TooHot", "Warm"}

natMin(a, b) == IF a < b THEN a ELSE b

TypeOK ==
    /\ tee \in Temps
    /\ primer \in Nat
    /\ dna \in Nat
    /\ template \in Nat
    /\ hybrid \in Nat
    /\ cycle \in Nat

Init ==
    /\ tee = "Hot"
    /\ primer = PRIMER
    /\ dna = DNA
    /\ template = 0
    /\ hybrid = 0
    /\ cycle = 0

(* Denaturation: high temperature melts double strands and hybrids into   *)
(* single strands; primers in melted hybrids are returned.                *)
heat ==
    /\ tee = "Hot"
    /\ tee' = "TooHot"
    /\ primer' = primer + hybrid
    /\ template' = template + hybrid + 2 * dna
    /\ dna' = 0
    /\ hybrid' = 0
    /\ UNCHANGED cycle

(* Intermediate temperature flip: only the temperature changes.           *)
cool ==
    /\ tee = "TooHot"
    /\ tee' = "Hot"
    /\ UNCHANGED <<primer, dna, template, hybrid, cycle>>

(* Annealing: primers bind to available single strands forming hybrids,  *)
(* bounded by available primers and templates.                            *)
anneal ==
    /\ tee = "Hot"
    /\ tee' = "Warm"
    /\ \E k \in 1..natMin(primer, template) :
         /\ primer' = primer - k
         /\ template' = template - k
         /\ hybrid' = hybrid + k
    /\ UNCHANGED <<dna, cycle>>

(* Extension: hybrids are converted into new double strands; completes a *)
(* cycle.                                                                 *)
extend ==
    /\ tee = "Warm"
    /\ tee' = "Hot"
    /\ dna' = dna + hybrid
    /\ hybrid' = 0
    /\ cycle' = cycle + 1
    /\ UNCHANGED <<primer, template>>

Next == heat \/ cool \/ anneal \/ extend

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(heat)
    /\ WF_vars(cool)
    /\ SF_vars(anneal)
    /\ WF_vars(extend)

cleanSpec ==
    /\ Spec
    /\ SF_vars(anneal)
    /\ WF_vars(extend)

-----------------------------------------------------------------------------
(* Correctness properties *)

\* (1) counts nonnegative, types in domain
NonNegative == /\ primer >= 0 /\ dna >= 0 /\ template >= 0 /\ hybrid >= 0

\* (2) primers nonincreasing except when returned by denaturation
PrimerMonotone ==
    [][ \/ primer' <= primer
        \/ (heat /\ primer' = primer + hybrid) ]_vars

\* (3) extension increases dna by at most the current number of hybrids
ExtendBound ==
    [][ (dna' > dna) => (dna' - dna <= hybrid) ]_vars

\* (4) enabled annealing eventually occurs; no illegal temperature moves
AnnealLiveness == []<>(ENABLED <<anneal>>_vars) => []<><<anneal>>_vars

LegalTransitions ==
    [][ \/ (tee = "Hot"    /\ tee' \in {"TooHot", "Warm"})
        \/ (tee = "TooHot" /\ tee' = "Hot" /\ UNCHANGED <<primer, dna, template, hybrid, cycle>>)
        \/ (tee = "Warm"   /\ tee' = "Hot") ]_vars

\* (5) primers eventually depleted
primerDepleted == <>(primer = 0)

\* (6) cycle counter increments exactly on completed extensions
CycleAccurate ==
    [][ (cycle' = cycle + 1 <=> extend) /\ (cycle' # cycle => extend) ]_vars

=============================================================================