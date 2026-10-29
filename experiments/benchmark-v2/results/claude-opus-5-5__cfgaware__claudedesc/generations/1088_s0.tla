---------------------------- MODULE apa ----------------------------
EXTENDS Naturals

CONSTANTS
    \* @type: Int;
    DNA,
    \* @type: Int;
    PRIMER

VARIABLES
    \* @type: Str;
    tee,
    \* @type: Int;
    primer,
    \* @type: Int;
    dna,
    \* @type: Int;
    template,
    \* @type: Int;
    hybrid

vars == << tee, primer, dna, template, hybrid >>

natMin(a, b) == IF a < b THEN a ELSE b

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
    /\ template' = template + hybrid + 2 * dna
    /\ dna' = 0
    /\ hybrid' = 0

cool ==
    /\ tee = "TooHot"
    /\ tee' = "Hot"
    /\ UNCHANGED << primer, dna, template, hybrid >>

anneal ==
    /\ tee = "Hot"
    /\ UNCHANGED tee
    /\ \E k \in 1..natMin(primer, template):
          /\ primer' = primer - k
          /\ template' = template - k
          /\ hybrid' = hybrid + k
          /\ UNCHANGED dna

extend ==
    /\ tee = "Hot"
    /\ UNCHANGED tee
    /\ dna' = dna + hybrid
    /\ hybrid' = 0
    /\ UNCHANGED << primer, template >>

Next == heat \/ cool \/ anneal \/ extend

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ tee \in {"Hot", "TooHot"}
    /\ primer \in Nat
    /\ dna \in Nat
    /\ template \in Nat
    /\ hybrid \in Nat

primerPositive == primer >= 0

preservationInvariant ==
    template + primer + 2 * (dna + hybrid) = PRIMER + 2 * DNA

=============================================================================