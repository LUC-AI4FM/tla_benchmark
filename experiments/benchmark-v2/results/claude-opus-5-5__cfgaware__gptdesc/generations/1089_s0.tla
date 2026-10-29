------------------------------ MODULE MC_stages ------------------------------
(***************************************************************************)
(* Apalache-typed wrapper for the "stages" PCR specification.  The         *)
(* original behaviour is reproduced inline so that the module is          *)
(* self-contained and passes SANY.                                         *)
(***************************************************************************)
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
    hybrid,
    \* @type: Str;
    stage

vars == << tee, primer, dna, template, hybrid, stage >>

natMin(i, j) == IF i < j THEN i ELSE j

Stages == {"init", "denatured", "annealed", "extended"}
Temps  == {"Cold", "Hot", "TooHot"}

TypeOK ==
    /\ tee \in Temps
    /\ primer \in Nat
    /\ dna \in Nat
    /\ template \in Nat
    /\ hybrid \in Nat
    /\ stage \in Stages

Init ==
    /\ tee = "Cold"
    /\ primer = PRIMER
    /\ dna = DNA
    /\ template = 0
    /\ hybrid = 0
    /\ stage = "init"

(* Heating separates double strands into single-strand templates. *)
Denature ==
    /\ stage \in {"init", "extended"}
    /\ tee' = "TooHot"
    /\ template' = template + 2 * dna
    /\ dna' = 0
    /\ stage' = "denatured"
    /\ UNCHANGED << primer, hybrid >>

(* Cooling lets primers bind to templates. *)
Anneal ==
    /\ stage = "denatured"
    /\ tee' = "Cold"
    /\ \E k \in 0..natMin(primer, template) :
          /\ hybrid' = hybrid + k
          /\ primer' = primer - k
          /\ template' = template - k
    /\ stage' = "annealed"
    /\ UNCHANGED dna

(* Warming lets the polymerase extend hybrids into double strands. *)
Extend ==
    /\ stage = "annealed"
    /\ tee' = "Hot"
    /\ dna' = dna + hybrid
    /\ hybrid' = 0
    /\ stage' = "extended"
    /\ UNCHANGED << primer, template >>

Next == Denature \/ Anneal \/ Extend

Spec == Init /\ [][Next]_vars

=============================================================================