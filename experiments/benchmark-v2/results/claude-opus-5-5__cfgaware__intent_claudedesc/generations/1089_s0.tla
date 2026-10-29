---------------------------- MODULE PCR ----------------------------
EXTENDS Naturals

CONSTANTS DNA,      \* initial number of double-stranded DNA molecules
          PRIMER    \* initial number of primers

ASSUME DNA \in Nat /\ PRIMER \in Nat

VARIABLES tee,       \* temperature of the reaction: "Warm", "Hot", "Cold"
          stage,     \* current stage of the protocol
          dna,       \* number of double-stranded DNA molecules
          primer,    \* number of free primers
          template,  \* number of single-stranded templates
          hybrid,    \* number of primer-template hybrids
          cycle      \* number of completed amplification cycles

vars == <<tee, stage, dna, primer, template, hybrid, cycle>>

Temps  == {"Warm", "Hot", "Cold"}
Stages == {"Ready", "Denatured", "Annealed", "Done"}

Min(a, b) == IF a < b THEN a ELSE b

TypeOK ==
    /\ tee \in Temps
    /\ stage \in Stages
    /\ dna \in Nat
    /\ primer \in Nat
    /\ template \in Nat
    /\ hybrid \in Nat
    /\ cycle \in Nat

Init ==
    /\ tee = "Warm"
    /\ stage = "Ready"
    /\ dna = DNA
    /\ primer = PRIMER
    /\ template = 0
    /\ hybrid = 0
    /\ cycle = 0

(* Denaturation: heating splits every double strand into two templates. *)
Denature ==
    /\ stage = "Ready"
    /\ primer > 0
    /\ dna + template > 0
    /\ tee' = "Hot"
    /\ stage' = "Denatured"
    /\ template' = template + 2 * dna
    /\ dna' = 0
    /\ UNCHANGED <<primer, hybrid, cycle>>

(* Annealing: cooling lets primers bind to templates, forming hybrids. *)
Anneal ==
    /\ stage = "Denatured"
    /\ tee = "Hot"
    /\ primer > 0
    /\ template > 0
    /\ \E k \in 1..Min(primer, template) :
          /\ template' = template - k
          /\ primer' = primer - k
          /\ hybrid' = hybrid + k
    /\ tee' = "Cold"
    /\ stage' = "Annealed"
    /\ UNCHANGED <<dna, cycle>>

(* Extension: polymerase extends every hybrid into a double strand. *)
Extend ==
    /\ stage = "Annealed"
    /\ tee = "Cold"
    /\ tee' = "Warm"
    /\ stage' = "Ready"
    /\ dna' = dna + hybrid
    /\ hybrid' = 0
    /\ cycle' = cycle + 1
    /\ UNCHANGED <<primer, template>>

(* The protocol finishes once no further amplification is possible. *)
Finish ==
    /\ stage = "Ready"
    /\ (primer = 0 \/ dna + template = 0)
    /\ stage' = "Done"
    /\ UNCHANGED <<tee, dna, primer, template, hybrid, cycle>>

(* Terminal state: stay done. *)
Halt ==
    /\ stage = "Done"
    /\ UNCHANGED vars

Next == Denature \/ Anneal \/ Extend \/ Finish \/ Halt

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------
(* Correctness properties *)

\* Temperature corresponds to the stage of the protocol.
StageTempOK ==
    /\ stage = "Denatured" => tee = "Hot"
    /\ stage = "Annealed"  => tee = "Cold"
    /\ stage \in {"Ready", "Done"} => tee = "Warm"

\* Hybrids exist only between annealing and extension.
HybridOK == stage # "Annealed" => hybrid = 0

\* After denaturation no double strands remain.
DenatureOK == stage = "Denatured" => dna = 0

\* Primers are conserved: free + bound-in-hybrid + incorporated never exceeds supply,
\* and each completed cycle consumed at least one primer.
PrimerOK ==
    /\ primer <= PRIMER
    /\ primer + hybrid <= PRIMER
    /\ cycle <= PRIMER - primer

\* Strand conservation: each primer used produces one new strand.
StrandOK == 2 * dna + template + 2 * hybrid = 2 * DNA + 2 * (PRIMER - primer) - hybrid + hybrid

\* Valid stage ordering.
StageOrder ==
    [][ \/ (stage = "Ready"     /\ stage' \in {"Denatured", "Done"})
        \/ (stage = "Denatured" /\ stage' = "Annealed")
        \/ (stage = "Annealed"  /\ stage' = "Ready" /\ cycle' = cycle + 1)
        \/ (stage = "Done"      /\ stage' = "Done") ]_vars

=====================================================================