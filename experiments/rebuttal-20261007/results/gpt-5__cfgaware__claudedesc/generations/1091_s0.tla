----------------------------- MODULE PCR -----------------------------
EXTENDS Naturals

CONSTANTS DNA, PRIMER

VARIABLES tee, primer, dna, template, hybrid

Temps == {"Hot", "TooHot", "Warm"}

vars == << tee, primer, dna, template, hybrid >>

TypeOK ==
  /\ tee \in Temps
  /\ primer \in Nat
  /\ dna \in Nat
  /\ template \in Nat
  /\ hybrid \in Nat

Init ==
  /\ tee = "Hot"
  /\ dna = DNA
  /\ primer = PRIMER
  /\ template = 0
  /\ hybrid = 0

Min(a, b) == IF a <= b THEN a ELSE b

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

Conserved == template + primer + 2 * (dna + hybrid)

primerPositive == primer >= 0

preservationInvariant == Conserved = PRIMER + 2 * DNA

preservationProperty == [](preservationInvariant)

Spec == Init /\ [][Next]_vars
=====================================================================