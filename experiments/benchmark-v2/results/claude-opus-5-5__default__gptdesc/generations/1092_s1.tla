------------------------------- MODULE PCR -------------------------------
EXTENDS Naturals

CONSTANTS
    Templates,   \* initial number of original double-stranded DNA molecules
    Primers,     \* initial primer supply
    MaxCycles    \* number of thermal cycles to perform

ASSUME TemplatesAssump == Templates \in Nat \ {0}
ASSUME PrimersAssump   == Primers \in Nat
ASSUME CyclesAssump    == MaxCycles \in Nat

VARIABLES
    temp,      \* current temperature: "low", "high", "anneal", "extend"
    stage,     \* current stage of the cycle
    cycle,     \* number of cycles started so far
    primer,    \* free primers available
    ssOrig,    \* single-stranded original templates
    ssLong,    \* single-stranded long (primer-started, unbounded end) templates
    ssShort,   \* single-stranded short (exact-length) templates
    hybOrig,   \* primer annealed to an original template
    hybLong,   \* primer annealed to a long template
    hybShort,  \* primer annealed to a short template
    dsOrig,    \* double-stranded original DNA (orig / orig)
    dsOL,      \* double-stranded orig / long
    dsLS,      \* double-stranded long / short
    product    \* final product: double-stranded short / short

vars == << temp, stage, cycle, primer, ssOrig, ssLong, ssShort,
           hybOrig, hybLong, hybShort, dsOrig, dsOL, dsLS, product >>

Temps  == {"low", "high", "anneal", "extend"}
Stages == {"init", "denatured", "cooled", "annealed", "extended"}

Min(a, b) == IF a <= b THEN a ELSE b

TypeOK ==
    /\ temp \in Temps
    /\ stage \in Stages
    /\ cycle \in Nat
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
    /\ temp = "low"
    /\ stage = "init"
    /\ cycle = 0
    /\ primer = Primers
    /\ ssOrig = 0
    /\ ssLong = 0
    /\ ssShort = 0
    /\ hybOrig = 0
    /\ hybLong = 0
    /\ hybShort = 0
    /\ dsOrig = Templates
    /\ dsOL = 0
    /\ dsLS = 0
    /\ product = 0

\* Denaturation: heating separates all double-stranded forms and hybrids
\* into single strands, and starts a new cycle.
Heat ==
    /\ stage \in {"init", "extended"}
    /\ cycle < MaxCycles
    /\ temp' = "high"
    /\ stage' = "denatured"
    /\ cycle' = cycle + 1
    /\ primer' = primer + hybOrig + hybLong + hybShort
    /\ ssOrig' = ssOrig + hybOrig + 2 * dsOrig + dsOL
    /\ ssLong' = ssLong + hybLong + dsOL + dsLS
    /\ ssShort' = ssShort + hybShort + dsLS + 2 * product
    /\ hybOrig' = 0
    /\ hybLong' = 0
    /\ hybShort' = 0
    /\ dsOrig' = 0
    /\ dsOL' = 0
    /\ dsLS' = 0
    /\ product' = 0

\* Cooling down after denaturation.
Cool ==
    /\ stage = "denatured"
    /\ temp' = "low"
    /\ stage' = "cooled"
    /\ UNCHANGED << cycle, primer, ssOrig, ssLong, ssShort,
                    hybOrig, hybLong, hybShort, dsOrig, dsOL, dsLS, product >>

\* Annealing: primers bind to single-stranded templates, limited by supply.
Anneal ==
    /\ stage = "cooled"
    /\ LET a1 == Min(ssOrig, primer)
           a2 == Min(ssLong, primer - a1)
           a3 == Min(ssShort, primer - a1 - a2)
       IN  /\ ssOrig' = ssOrig - a1
           /\ ssLong' = ssLong - a2
           /\ ssShort' = ssShort - a3
           /\ hybOrig' = hybOrig + a1
           /\ hybLong' = hybLong + a2
           /\ hybShort' = hybShort + a3
           /\ primer' = primer - a1 - a2 - a3
    /\ temp' = "anneal"
    /\ stage' = "annealed"
    /\ UNCHANGED << cycle, dsOrig, dsOL, dsLS, product >>

\* Extension: polymerase extends primers along their templates.
\*   original template + primer -> orig/long double strand
\*   long template     + primer -> long/short double strand
\*   short template    + primer -> short/short final product
Extend ==
    /\ stage = "annealed"
    /\ temp' = "extend"
    /\ stage' = "extended"
    /\ dsOL' = dsOL + hybOrig
    /\ dsLS' = dsLS + hybLong
    /\ product' = product + hybShort
    /\ hybOrig' = 0
    /\ hybLong' = 0
    /\ hybShort' = 0
    /\ UNCHANGED << cycle, primer, ssOrig, ssLong, ssShort, dsOrig >>

\* Process finished: all cycles done.
Done ==
    /\ stage \in {"init", "extended"}
    /\ cycle >= MaxCycles
    /\ UNCHANGED vars

Next == Heat \/ Cool \/ Anneal \/ Extend \/ Done

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Heat)
    /\ WF_vars(Cool)
    /\ WF_vars(Anneal)
    /\ WF_vars(Extend)

-----------------------------------------------------------------------------
\* Safety: no final product exists before the third cycle.
NoEarlyProduct == (cycle < 3) => (product = 0)

\* Liveness: all requested cycles are eventually performed.
AllCyclesComplete == <>(cycle = MaxCycles /\ stage = "extended")

THEOREM Spec => [](TypeOK /\ NoEarlyProduct)
=============================================================================