----------------------------- MODULE PCRCycle -----------------------------
EXTENDS Naturals, Integers

CONSTANTS
  P0,   \* initial primers
  DS0,  \* initial double-stranded DNA
  SS0,  \* initial single-stranded templates
  HY0   \* initial template-primer hybrids

VARIABLES
  phase,      \* one of "Heat","Cool","Anneal","Extend"
  temp,       \* one of "Hot","Cold"
  primers,    \* count of primers
  dsDNA,      \* count of double-stranded DNA molecules
  templates,  \* count of single-stranded templates
  hybrids     \* count of template-primer hybrids

PhaseSet == {"Heat", "Cool", "Anneal", "Extend"}
TempSet  == {"Hot", "Cold"}

Min(a, b) == IF a <= b THEN a ELSE b

TypeOK ==
  /\ phase \in PhaseSet
  /\ temp \in TempSet
  /\ primers \in Nat
  /\ dsDNA \in Nat
  /\ templates \in Nat
  /\ hybrids \in Nat

NonNeg ==
  /\ primers >= 0
  /\ dsDNA >= 0
  /\ templates >= 0
  /\ hybrids >= 0

CountPreserved ==
  templates + hybrids + dsDNA = SS0 + HY0 + DS0

Init ==
  /\ phase = "Heat"
  /\ temp = "Hot"
  /\ primers = P0
  /\ dsDNA = DS0
  /\ templates = SS0
  /\ hybrids = HY0

Heat ==
  /\ phase = "Heat"
  /\ phase' = "Cool"
  /\ temp' = "Hot"
  /\ UNCHANGED << primers, dsDNA, templates, hybrids >>

Cool ==
  /\ phase = "Cool"
  /\ phase' = "Anneal"
  /\ temp' = "Cold"
  /\ UNCHANGED << primers, dsDNA, templates, hybrids >>

Anneal ==
  /\ phase = "Anneal"
  /\ \E k \in 0..Min(primers, templates):
       /\ primers' = primers - k
       /\ templates' = templates - k
       /\ hybrids' = hybrids + k
       /\ dsDNA' = dsDNA
       /\ temp' = temp
       /\ phase' = "Extend"

Extend ==
  /\ phase = "Extend"
  /\ \E k \in 0..hybrids:
       /\ hybrids' = hybrids - k
       /\ dsDNA' = dsDNA + k
       /\ UNCHANGED << primers, templates >>
       /\ temp' = temp
       /\ phase' = "Heat"

Next == Heat \/ Cool \/ Anneal \/ Extend

vars == << phase, temp, primers, dsDNA, templates, hybrids >>

Spec == Init /\ [][Next]_vars

\* Safety invariants to be checked under Spec
InvTypeOK == TypeOK
InvNonNeg == NonNeg
InvCountPreserved == CountPreserved

\* Liveness property claiming eventual primer depletion (does not hold in general)
PrimerDepletion == <> (primers = 0)
=============================================================================