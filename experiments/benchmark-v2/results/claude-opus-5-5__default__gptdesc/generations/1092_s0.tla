---------------------------- MODULE PCRProductGeneration ----------------------------
(***************************************************************************)
(* A PCR-like product generation process across repeated temperature      *)
(* cycles.                                                                 *)
(*                                                                         *)
(* Strand classes:                                                         *)
(*   tmpl     : original single-stranded templates (unbounded ends)        *)
(*   longS    : single strands made by extending a primer on an original   *)
(*              template (one end defined by a primer)                     *)
(*   shortS   : single strands with both ends defined by primers           *)
(*                                                                         *)
(* Hybridized intermediates (strand + annealed primer):                    *)
(*   tmplHyb, longHyb, shortHyb                                            *)
(*                                                                         *)
(* Double-stranded forms:                                                  *)
(*   dsTmpl   : original template duplex                                   *)
(*   dsLong   : original template paired with a long strand                *)
(*   dsMed    : long strand paired with a short strand                     *)
(*   product  : short strand paired with short strand (final product)      *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    InitTemplates,   \* number of original double-stranded templates
    InitPrimers,     \* initial primer supply
    MaxCycles        \* number of thermal cycles to run

ASSUME /\ InitTemplates \in Nat \ {0}
       /\ InitPrimers \in Nat
       /\ MaxCycles \in Nat

VARIABLES
    temp,       \* current temperature
    stage,      \* current stage of the cycle
    cycle,      \* number of cycles started
    primers,    \* free primer supply
    tmpl,       \* single-stranded original templates
    longS,      \* single-stranded long strands
    shortS,     \* single-stranded short strands
    tmplHyb,    \* original template + primer
    longHyb,    \* long strand + primer
    shortHyb,   \* short strand + primer
    dsTmpl,     \* original duplex
    dsLong,     \* template : long duplex
    dsMed,      \* long : short duplex
    product     \* short : short duplex (final product)

vars == << temp, stage, cycle, primers, tmpl, longS, shortS,
           tmplHyb, longHyb, shortHyb, dsTmpl, dsLong, dsMed, product >>

Temps  == {25, 95, 55, 72}
Stages == {"init", "denatured", "cooled", "annealed", "extended"}

Min(a, b) == IF a <= b THEN a ELSE b

-----------------------------------------------------------------------------

TypeOK ==
    /\ temp \in Temps
    /\ stage \in Stages
    /\ cycle \in 0..MaxCycles
    /\ primers \in Nat
    /\ tmpl \in Nat
    /\ longS \in Nat
    /\ shortS \in Nat
    /\ tmplHyb \in Nat
    /\ longHyb \in Nat
    /\ shortHyb \in Nat
    /\ dsTmpl \in Nat
    /\ dsLong \in Nat
    /\ dsMed \in Nat
    /\ product \in Nat

Init ==
    /\ temp = 25
    /\ stage = "init"
    /\ cycle = 0
    /\ primers = InitPrimers
    /\ tmpl = 0
    /\ longS = 0
    /\ shortS = 0
    /\ tmplHyb = 0
    /\ longHyb = 0
    /\ shortHyb = 0
    /\ dsTmpl = InitTemplates
    /\ dsLong = 0
    /\ dsMed = 0
    /\ product = 0

-----------------------------------------------------------------------------

(* Heat: start a new cycle, denature all double-stranded forms. *)
Heat ==
    /\ stage \in {"init", "extended"}
    /\ cycle < MaxCycles
    /\ temp' = 95
    /\ stage' = "denatured"
    /\ cycle' = cycle + 1
    /\ tmpl'   = tmpl + 2 * dsTmpl + dsLong
    /\ longS'  = longS + dsLong + dsMed
    /\ shortS' = shortS + dsMed + 2 * product
    /\ dsTmpl'  = 0
    /\ dsLong'  = 0
    /\ dsMed'   = 0
    /\ product' = 0
    /\ UNCHANGED << primers, tmplHyb, longHyb, shortHyb >>

(* Cool: lower temperature to annealing temperature. *)
Cool ==
    /\ stage = "denatured"
    /\ temp' = 55
    /\ stage' = "cooled"
    /\ UNCHANGED << cycle, primers, tmpl, longS, shortS, tmplHyb, longHyb,
                    shortHyb, dsTmpl, dsLong, dsMed, product >>

(* Anneal: primers bind to available single strands, limited by supply. *)
Anneal ==
    /\ stage = "cooled"
    /\ LET a  == Min(primers, tmpl)
           r1 == primers - a
           b  == Min(r1, longS)
           r2 == r1 - b
           c  == Min(r2, shortS)
       IN  /\ primers'  = r2 - c
           /\ tmpl'     = tmpl - a
           /\ longS'    = longS - b
           /\ shortS'   = shortS - c
           /\ tmplHyb'  = tmplHyb + a
           /\ longHyb'  = longHyb + b
           /\ shortHyb' = shortHyb + c
    /\ stage' = "annealed"
    /\ UNCHANGED << temp, cycle, dsTmpl, dsLong, dsMed, product >>

(* Extend: polymerase extends annealed primers, forming duplexes. *)
Extend ==
    /\ stage = "annealed"
    /\ temp' = 72
    /\ stage' = "extended"
    /\ dsLong'  = dsLong + tmplHyb
    /\ dsMed'   = dsMed + longHyb
    /\ product' = product + shortHyb
    /\ tmplHyb'  = 0
    /\ longHyb'  = 0
    /\ shortHyb' = 0
    /\ UNCHANGED << cycle, primers, tmpl, longS, shortS, dsTmpl >>

(* Process finished: stutter to avoid spurious deadlock. *)
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

-----------------------------------------------------------------------------

(* Safety: no final product exists before the third cycle. *)
NoProductBeforeThirdCycle == cycle < 3 => product = 0

THEOREM Spec => [](TypeOK /\ NoProductBeforeThirdCycle)

=============================================================================