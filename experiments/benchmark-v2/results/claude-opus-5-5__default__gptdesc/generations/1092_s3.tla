---------------------------- MODULE PCRProduct ----------------------------
EXTENDS Naturals

CONSTANTS
    InitDNA,      \* number of original double-stranded template molecules
    InitPrimers,  \* initial primer supply
    MaxCycles     \* number of thermal cycles to run

ASSUME InitDNA \in Nat /\ InitPrimers \in Nat /\ MaxCycles \in Nat

VARIABLES
    temp,       \* current temperature
    stage,      \* current stage of the cycle
    cycle,      \* number of cycles started
    primer,     \* free primers
    ssOrig,     \* single-stranded original template strands
    ssLong,     \* single strands with one defined end (from extending on original)
    ssShort,    \* single strands with both ends defined (from extending on long)
    hybOrig,    \* original strand + annealed primer
    hybLong,    \* long strand + annealed primer
    hybShort,   \* short strand + annealed primer
    dsOrig,     \* original double-stranded DNA
    dsOL,       \* duplex: original strand paired with long strand
    dsLS,       \* duplex: long strand paired with short strand
    product     \* final product: short strand paired with short strand

vars == << temp, stage, cycle, primer, ssOrig, ssLong, ssShort,
           hybOrig, hybLong, hybShort, dsOrig, dsOL, dsLS, product >>

Min(a, b) == IF a <= b THEN a ELSE b

Temps  == {25, 95, 55, 72}
Stages == {"init", "denatured", "cooled", "annealed", "extended"}

TypeOK ==
    /\ temp \in Temps
    /\ stage \in Stages
    /\ cycle \in 0..MaxCycles
    /\ primer \in Nat
    /\ ssOrig \in Nat
    /\ ssLong \in Nat
    /\ ssShort \in Nat
    /\ hybOrig \in Nat
    /\ hybLong \in Nat
    /\ hybShort \in Nat
    /\ dsOrig \in Nat
    /\ dsOL \in Nat
    /\ dsLS \in Nat
    /\ product \in Nat

Init ==
    /\ temp = 25
    /\ stage = "init"
    /\ cycle = 0
    /\ primer = InitPrimers
    /\ ssOrig = 0
    /\ ssLong = 0
    /\ ssShort = 0
    /\ hybOrig = 0
    /\ hybLong = 0
    /\ hybShort = 0
    /\ dsOrig = InitDNA
    /\ dsOL = 0
    /\ dsLS = 0
    /\ product = 0

\* Denaturation: all double-stranded forms separate into single strands.
Heat ==
    /\ stage \in {"init", "extended"}
    /\ cycle < MaxCycles
    /\ temp' = 95
    /\ stage' = "denatured"
    /\ cycle' = cycle + 1
    /\ ssOrig'  = ssOrig + hybOrig + 2 * dsOrig + dsOL
    /\ ssLong'  = ssLong + hybLong + dsOL + dsLS
    /\ ssShort' = ssShort + hybShort + dsLS + 2 * product
    /\ primer'  = primer + hybOrig + hybLong + hybShort
    /\ hybOrig' = 0
    /\ hybLong' = 0
    /\ hybShort' = 0
    /\ dsOrig' = 0
    /\ dsOL' = 0
    /\ dsLS' = 0
    /\ product' = 0

\* Cooling to annealing temperature.
Cool ==
    /\ stage = "denatured"
    /\ temp' = 55
    /\ stage' = "cooled"
    /\ UNCHANGED << cycle, primer, ssOrig, ssLong, ssShort,
                    hybOrig, hybLong, hybShort, dsOrig, dsOL, dsLS, product >>

\* Annealing: primers bind to single strands, limited by primer supply.
Anneal ==
    /\ stage = "cooled"
    /\ LET a1 == Min(ssOrig, primer)
           a2 == Min(ssLong, primer - a1)
           a3 == Min(ssShort, primer - a1 - a2)
       IN /\ primer'   = primer - a1 - a2 - a3
          /\ ssOrig'   = ssOrig - a1
          /\ ssLong'   = ssLong - a2
          /\ ssShort'  = ssShort - a3
          /\ hybOrig'  = hybOrig + a1
          /\ hybLong'  = hybLong + a2
          /\ hybShort' = hybShort + a3
    /\ stage' = "annealed"
    /\ UNCHANGED << temp, cycle, dsOrig, dsOL, dsLS, product >>

\* Extension: polymerase extends primers, forming double-stranded forms.
Extend ==
    /\ stage = "annealed"
    /\ temp' = 72
    /\ stage' = "extended"
    /\ dsOL'     = dsOL + hybOrig
    /\ dsLS'     = dsLS + hybLong
    /\ product'  = product + hybShort
    /\ hybOrig'  = 0
    /\ hybLong'  = 0
    /\ hybShort' = 0
    /\ UNCHANGED << cycle, primer, ssOrig, ssLong, ssShort, dsOrig >>

\* Process finished after the last cycle.
Done ==
    /\ stage \in {"init", "extended"}
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

\* Safety: no final product exists before the third cycle.
NoProductBeforeCycle3 == cycle < 3 => product = 0

THEOREM Spec => [](TypeOK /\ NoProductBeforeCycle3)
=============================================================================