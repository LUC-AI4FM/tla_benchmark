------------------------------ MODULE PCR ------------------------------
EXTENDS Naturals

(* Helper function *)
Min(a,b) == IF a <= b THEN a ELSE b

TypeOK ==
  /\ temp \in {95,65,72}
  /\ primers >= 0
  /\ dna >= 0
  /\ templates >= 0
  /\ hybrids >= 0

primerPositive == primers > 0

preservationInvariant ==
  primers + templates + hybrids + dna = 15

preservationProperty == [] preservationInvariant

VARIABLES temp, primers, dna, templates, hybrids

Init ==
  /\ temp = 95
  /\ primers = 10
  /\ dna = 0
  /\ templates = 5
  /\ hybrids = 0

Heating ==
  /\ temp' = 95
  /\ temp != 95
  /\ UNCHANGED <<primers, dna, templates, hybrids>>

Cooling ==
  /\ temp' = 65
  /\ temp != 65
  /\ UNCHANGED <<primers, dna, templates, hybrids>>

SetTemp72 ==
  /\ temp' = 72
  /\ temp != 72
  /\ UNCHANGED <<primers, dna, templates, hybrids>>

Annealing ==
  /\ temp = 65
  /\ primers > 0
  /\ templates > 0
  /\ LET k == CHOOSE n \in Nat : n <= Min(primers, templates) IN
     /\ k >= 1
     /\ primers' = primers - k
     /\ templates' = templates - k
     /\ hybrids' = hybrids + k
     /\ dna' = dna

Extension ==
  /\ temp = 72
  /\ hybrids > 0
  /\ UNCHANGED <<temp, primers, templates>>
  /\ dna' = dna + hybrids
  /\ hybrids' = 0

Next == Heating \/ Cooling \/ SetTemp72 \/ Annealing \/ Extension

Spec == Init /\ [][Next]_<<temp, primers, dna, templates, hybrids>>

(* Liveness property (does not hold) *)
(* []<> (primers = 0) *)

=============================================================================