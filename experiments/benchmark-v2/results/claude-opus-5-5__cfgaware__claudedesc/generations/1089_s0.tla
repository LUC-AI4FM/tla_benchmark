------------------------------- MODULE MC_stages -------------------------------
(***************************************************************************)
(* Type-annotated wrapper for the staged PCR (Polymerase Chain Reaction)   *)
(* specification.  The behavior of the original `stages` module is         *)
(* reproduced inline so that this module is self-contained and parses on   *)
(* its own.                                                                *)
(***************************************************************************)
EXTENDS Integers

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
    hybrid,
    \* @type: Str;
    stage,
    \* @type: Int;
    cycle

vars == << tee, primer, dna, template, hybrid, stage, cycle >>

Min(a, b) == IF a < b THEN a ELSE b

Temperatures == {"Hot", "TooHot", "Warm"}
Stages       == {"init", "denatured", "annealed", "extended"}

TypeOK ==
    /\ tee \in Temperatures
    /\ primer \in Nat
    /\ dna \in Nat
    /\ template \in Nat
    /\ hybrid \in Nat
    /\ stage \in Stages
    /\ cycle \in Nat

Init ==
    /\ tee = "Warm"
    /\ primer = PRIMER
    /\ dna = DNA
    /\ template = 0
    /\ hybrid = 0
    /\ stage = "init"
    /\ cycle = 0

(* Heating: every double strand separates into two templates. *)
Denature ==
    /\ stage \in {"init", "extended"}
    /\ tee' = "TooHot"
    /\ template' = template + 2 * dna
    /\ dna' = 0
    /\ stage' = "denatured"
    /\ UNCHANGED << primer, hybrid, cycle >>

(* Cooling: primers bind to templates, forming hybrids. *)
Anneal ==
    /\ stage = "denatured"
    /\ primer > 0
    /\ template > 0
    /\ \E k \in 1..Min(primer, template) :
          /\ primer' = primer - k
          /\ template' = template - k
          /\ hybrid' = hybrid + k
    /\ tee' = "Hot"
    /\ stage' = "annealed"
    /\ UNCHANGED << dna, cycle >>

(* Warming: polymerase extends hybrids into full double strands. *)
Extend ==
    /\ stage = "annealed"
    /\ tee' = "Warm"
    /\ dna' = dna + hybrid
    /\ hybrid' = 0
    /\ stage' = "extended"
    /\ cycle' = cycle + 1
    /\ UNCHANGED << primer, template >>

Next == Denature \/ Anneal \/ Extend

Spec == Init /\ [][Next]_vars

\* Conservation of primer-derived strand material.
Conservation ==
    2 * dna + template + 2 * hybrid + primer = 2 * DNA + PRIMER

=============================================================================