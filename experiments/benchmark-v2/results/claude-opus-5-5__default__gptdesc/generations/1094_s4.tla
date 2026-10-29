------------------------------- MODULE stages -------------------------------
EXTENDS Naturals

CONSTANTS DNA, PRIMER

ASSUME DNA \in Nat /\ PRIMER \in Nat

VARIABLES tee, primer, dna, template, hybrid, stage, cycle

-------------------------------- MODULE clean --------------------------------
EXTENDS Naturals

CONSTANTS DNA, PRIMER

VARIABLES tee, primer, dna, template, hybrid

cvars == << tee, primer, dna, template, hybrid >>

natMin(i, j) == IF i < j THEN i ELSE j

TypeOK ==
    /\ tee \in {"Hot", "TooHot", "Warm"}
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

heat ==
    /\ tee = "Hot"
    /\ tee' = "TooHot"
    /\ primer' = primer + hybrid
    /\ dna' = 0
    /\ template' = template + hybrid + 2 * dna
    /\ hybrid' = 0

cool ==
    /\ tee = "TooHot"
    /\ tee' = "Hot"
    /\ UNCHANGED << primer, dna, template, hybrid >>

anneal ==
    /\ tee = "Hot"
    /\ tee' = "Warm"
    /\ \E k \in 0..natMin(primer, template) :
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

Spec == Init /\ [][Next]_cvars /\ WF_cvars(Next)

Conservation ==
    primer + 2 * dna + template + 2 * hybrid = PRIMER + 2 * DNA

Safety == [](TypeOK /\ Conservation)

Liveness == []<>(tee = "Hot")
==============================================================================