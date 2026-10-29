------------------------------- MODULE PCR -------------------------------
EXTENDS Naturals

CONSTANTS
    InitTemplates,   \* number of original double-stranded template molecules
    InitPrimers,     \* initial primer supply
    MaxCycles        \* number of thermal cycles to perform

ASSUME /\ InitTemplates \in Nat \ {0}
       /\ InitPrimers \in Nat
       /\ MaxCycles \in Nat

VARIABLES
    temp,        \* current temperature
    stage,       \* current stage of the thermal cycle
    cycle,       \* number of cycles started so far
    primers,     \* free primers available
    ssOrig,      \* single-stranded original template strands
    ssLong,      \* single strands with one defined (primer) end
    ssShort,     \* single strands of exact target length (both ends defined)
    hybOrig,     \* primer hybridized to an original strand
    hybLong,     \* primer hybridized to a long strand
    hybShort,    \* primer hybridized to a short strand
    dsOrig,      \* double-stranded original template
    dsOrigLong,  \* duplex of original strand and long strand
    dsLongShort, \* duplex of long strand and short strand
    product      \* final product: duplex of two exact-length strands

vars == << temp, stage, cycle, primers,
           ssOrig, ssLong, ssShort,
           hybOrig, hybLong, hybShort,
           dsOrig, dsOrigLong, dsLongShort, product >>

Temps  == {25, 55, 72, 95}
Stages == {"init", "denatured", "cooled", "annealed", "extended"}

TypeOK ==
    /\ temp \in Temps
    /\ stage \in Stages
    /\ cycle \in 0..MaxCycles
    /\ primers \in Nat
    /\ ssOrig \in Nat
    /\ ssLong \in Nat
    /\ ssShort \in Nat
    /\ hybOrig \in Nat
    /\ hybLong \in Nat
    /\ hybShort \in Nat
    /\ dsOrig \in Nat
    /\ dsOrigLong \in Nat
    /\ dsLongShort \in Nat
    /\ product \in Nat

Init ==
    /\ temp = 25
    /\ stage = "init"
    /\ cycle = 0
    /\ primers = InitPrimers
    /\ ssOrig = 0
    /\ ssLong = 0
    /\ ssShort = 0
    /\ hybOrig = 0
    /\ hybLong = 0
    /\ hybShort = 0
    /\ dsOrig = InitTemplates
    /\ dsOrigLong = 0
    /\ dsLongShort = 0
    /\ product = 0

(* Heating: start a new cycle and denature all double-stranded and          *)
(* hybridized forms into single strands (primers released from hybrids).   *)
Heat ==
    /\ stage \in {"init", "extended"}
    /\ cycle < MaxCycles
    /\ temp' = 95
    /\ stage' = "denatured"
    /\ cycle' = cycle + 1
    /\ primers' = primers + hybOrig + hybLong + hybShort
    /\ ssOrig'  = ssOrig + 2 * dsOrig + dsOrigLong + hybOrig
    /\ ssLong'  = ssLong + dsOrigLong + dsLongShort + hybLong
    /\ ssShort' = ssShort + dsLongShort + 2 * product + hybShort
    /\ hybOrig' = 0
    /\ hybLong' = 0
    /\ hybShort' = 0
    /\ dsOrig' = 0
    /\ dsOrigLong' = 0
    /\ dsLongShort' = 0
    /\ product' = 0

(* Cooling to the annealing temperature. *)
Cool ==
    /\ stage = "denatured"
    /\ temp' = 55
    /\ stage' = "cooled"
    /\ UNCHANGED << cycle, primers, ssOrig, ssLong, ssShort,
                    hybOrig, hybLong, hybShort,
                    dsOrig, dsOrigLong, dsLongShort, product >>

(* Annealing: primers bind to some single strands, limited by supply. *)
Anneal ==
    /\ stage = "cooled"
    /\ \E a \in 0..ssOrig, b \in 0..ssLong, c \in 0..ssShort :
          /\ a + b + c <= primers
          /\ primers' = primers - (a + b + c)
          /\ ssOrig'  = ssOrig - a
          /\ ssLong'  = ssLong - b
          /\ ssShort' = ssShort - c
          /\ hybOrig'  = hybOrig + a
          /\ hybLong'  = hybLong + b
          /\ hybShort' = hybShort + c
    /\ stage' = "annealed"
    /\ UNCHANGED << temp, cycle, dsOrig, dsOrigLong, dsLongShort, product >>

(* Extension: polymerase extends each primer along its template.           *)
(*   primer on original -> long strand,  yielding orig/long duplex          *)
(*   primer on long     -> short strand, yielding long/short duplex         *)
(*   primer on short    -> short strand, yielding the final product         *)
Extend ==
    /\ stage = "annealed"
    /\ temp' = 72
    /\ stage' = "extended"
    /\ dsOrigLong'  = dsOrigLong + hybOrig
    /\ dsLongShort' = dsLongShort + hybLong
    /\ product'     = product + hybShort
    /\ hybOrig' = 0
    /\ hybLong' = 0
    /\ hybShort' = 0
    /\ UNCHANGED << cycle, primers, ssOrig, ssLong, ssShort, dsOrig >>

(* All cycles complete: the system stutters. *)
Done ==
    /\ stage = "extended"
    /\ cycle = MaxCycles
    /\ UNCHANGED vars

Next == Heat \/ Cool \/ Anneal \/ Extend \/ Done

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Heat)
    /\ WF_vars(Cool)
    /\ WF_vars(Anneal)
    /\ WF_vars(Extend)

(* Safety: no final product exists before the third cycle. *)
NoEarlyProduct == (cycle < 3) => (product = 0)

THEOREM Spec => [](TypeOK /\ NoEarlyProduct)
=============================================================================