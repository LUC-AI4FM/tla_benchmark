---------------------------- MODULE APAclean ----------------------------
(***************************************************************************)
(* Apalache annotation wrapper around the specification "clean".           *)
(* The type annotations live here, in comments, so that the original       *)
(* specification can stay free of tool-specific annotations.               *)
(*                                                                         *)
(* The original module would be instantiated with:                         *)
(*     INSTANCE clean                                                      *)
(* This module repeats the behavior of clean so that it can be parsed by   *)
(* SANY on its own, without the file clean.tla.                            *)
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
    hybrid

ASSUME DNA \in Nat /\ PRIMER \in Nat

vars == << tee, primer, dna, template, hybrid >>

natMin(i, j) == IF i < j THEN i ELSE j

TypeOK ==
    /\ tee \in {"Hot", "Cool", "Warm"}
    /\ primer \in Nat
    /\ dna \in Nat
    /\ template \in Nat
    /\ hybrid \in Nat

Init ==
    /\ tee = "Hot"
    /\ primer = PRIMER
    /\ dna = DNA
    /\ template = 0
    /\ hybrid = 0

(* Denaturation: double strands separate into single-stranded templates,   *)
(* and hybrids release their primers.                                      *)
heat ==
    /\ tee = "Warm"
    /\ tee' = "Hot"
    /\ primer' = primer + hybrid
    /\ template' = template + hybrid + 2 * dna
    /\ dna' = 0
    /\ hybrid' = 0

(* Annealing: some primers bind to templates, forming hybrids.             *)
cool ==
    /\ tee = "Hot"
    /\ tee' = "Cool"
    /\ \E k \in 0..natMin(primer, template) :
          /\ primer' = primer - k
          /\ template' = template - k
          /\ hybrid' = hybrid + k
    /\ UNCHANGED dna

(* Extension: hybrids are extended into full double-stranded DNA.          *)
extend ==
    /\ tee = "Cool"
    /\ tee' = "Warm"
    /\ dna' = dna + hybrid
    /\ hybrid' = 0
    /\ UNCHANGED << primer, template >>

Next == heat \/ cool \/ extend

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* Safety *)
PrimerBound == primer <= PRIMER + hybrid + dna + template + DNA

Safety == TypeOK /\ primer <= PRIMER

(* Liveness: the thermal cycle keeps going *)
CycleProgress == []<>(tee = "Hot")

THEOREM Spec => []TypeOK
=============================================================================