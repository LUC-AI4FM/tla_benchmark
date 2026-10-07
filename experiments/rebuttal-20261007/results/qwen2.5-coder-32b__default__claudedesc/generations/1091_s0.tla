------------------------------- MODULE PCR -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS DNA, PRIMER

VARIABLES tee, primer, dna, template, hybrid

Init == 
  /\ tee = "Hot"
  /\ primer = PRIMER
  /\ dna = DNA
  /\ template = 0
  /\ hybrid = 0

TypeOK ==
  \/ tee = "Hot"
  \/ tee = "TooHot"
  \/ tee = "Warm"

heat ==
  \E d \in 1..dna, h \in 0..hybrid :
    /\ tee = "Hot"
    /\ primer' = primer + h
    /\ dna' = dna - d
    /\ template' = template + d + h
    /\ hybrid' = 0
    /\ tee' = "TooHot"

cool ==
  tee = "TooHot" /\ tee' = "Hot"

anneal ==
  \E p \in 1..primer, t \in 1..template :
    /\ tee = "Hot"
    /\ primer' = primer - p
    /\ dna' = dna
    /\ template' = template - t
    /\ hybrid' = hybrid + [p -> t]
    /\ tee' = "Warm"

extend ==
  tee = "Warm" /\ 
  primer' = primer /\ 
  dna' = dna + Cardinality(hybrid) /\ 
  template' = template - Cardinality(hybrid) /\ 
  hybrid' = {} /\ 
  tee' = "Hot"

Next == heat \/ cool \/ anneal \/ extend

Spec ==
  Init /\ [][Next]_<<tee, primer, dna, template, hybrid>> /\ WF_next(<<tee, primer, dna, template, hybrid>>)

TypeInvariant == [](TypeOK)
NonNegativityInvariant == [](\A v \in {primer, dna, template, hybrid} : v >= 0)
ConservationLaw == [](template + primer + 2*(dna + Cardinality(hybrid))) = (PRIMER + 2*DNA)
StutteringTolerantSafety == <>([]((template + primer + 2*(dna + Cardinality(hybrid))) = (PRIMER + 2*DNA)))
PrimerDepletionLiveness == <>(primer' = 0)

=============================================================================