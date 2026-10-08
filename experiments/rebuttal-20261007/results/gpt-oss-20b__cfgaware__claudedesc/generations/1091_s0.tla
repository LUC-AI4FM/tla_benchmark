------------------------------ MODULE PCR ------------------------------
EXTENDS Naturals

CONSTANTS DNA, PRIMER

VARIABLES tee, primer, dna, template, hybrid

vars == <<tee, primer, dna, template, hybrid>>

Init ==
  /\ tee = "Hot"
  /\ dna = DNA
  /\ primer = PRIMER
  /\ template = 0
  /\ hybrid = 0

heat ==
  /\ tee = "Hot"
  /\ tee' = "TooHot"
  /\ dna' = 0
  /\ hybrid' = 0
  /\ template' = template + dna + hybrid
  /\ primer' = primer + hybrid

cool ==
  /\ tee = "TooHot"
  /\ tee' = "Hot"

anneal ==
  /\ tee = "Hot"
  /\ tee' = "Warm"
  /\ \E k \in Nat :
        k <= primer
        /\ k <= template
        /\ primer' = primer - k
        /\ template' = template - k
        /\ hybrid' = hybrid + k

extend ==
  /\ tee = "Warm"
  /\ tee' = "Hot"
  /\ dna' = dna + hybrid
  /\ hybrid' = 0

Next == heat \/ cool \/ anneal \/ extend

TypeOK ==
  /\ tee \in {"Hot", "TooHot", "Warm"}
  /\ dna \in Nat
  /\ primer \in Nat
  /\ template \in Nat
  /\ hybrid \in Nat

primerPositive == primer >= 0

preservationInvariant ==
  template + primer + 2 * (dna + hybrid) = PRIMER + 2 * DNA

preservationProperty == [] preservationInvariant

Spec == Init /\ [][Next]_vars

(* Optional liveness property *)
PrimerDepletion == <> (primer = 0)

=============================================================================