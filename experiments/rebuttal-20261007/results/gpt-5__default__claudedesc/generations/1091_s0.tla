----------------------------- MODULE PCR -----------------------------

EXTENDS Naturals, Integers

CONSTANTS DNA, PRIMER

VARIABLES tee, primer, dna, template, hybrid

vars == << tee, primer, dna, template, hybrid >>

Min(a, b) == IF a <= b THEN a ELSE b

Init ==
  /\ tee = "Hot"
  /\ dna = DNA
  /\ primer = PRIMER
  /\ template = 0
  /\ hybrid = 0

TypeOK ==
  /\ tee \in {"Hot", "TooHot", "Warm"}
  /\ primer \in Nat
  /\ dna \in Nat
  /\ template \in Nat
  /\ hybrid \in Nat
  /\ DNA \in Nat
  /\ PRIMER \in Nat

NonNegPrimers == primer >= 0

ConsLaw == template + primer + 2 * (dna + hybrid) = PRIMER + 2 * DNA

heat ==
  /\ tee = "Hot"
  /\ tee' = "TooHot"
  /\ dna' = 0
  /\ hybrid' = 0
  /\ template' = template + 2 * dna + hybrid
  /\ primer' = primer + hybrid

cool ==
  /\ tee = "TooHot"
  /\ tee' = "Hot"
  /\ UNCHANGED << primer, dna, template, hybrid >>

anneal ==
  /\ tee = "Hot"
  /\ tee' = "Warm"
  /\ \E k \in 0 .. Min(primer, template):
       /\ primer' = primer - k
       /\ template' = template - k
       /\ hybrid' = hybrid + k
       /\ UNCHANGED dna

extend ==
  /\ tee = "Warm"
  /\ tee' = "Hot"
  /\ dna' = dna + hybrid
  /\ hybrid' = 0
  /\ UNCHANGED << primer, template >>

Next == heat \/ cool \/ anneal \/ extend

Spec == Init /\ [][Next]_vars

ConservationSafety == [](ConsLaw)

PrimerDepletion == <>(primer = 0)
=====================================================================