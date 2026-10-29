---------------------------- MODULE typedclean ----------------------------
(***************************************************************************)
(* Type-annotated version of the `clean` PCR (polymerase chain reaction)   *)
(* specification, written for the Apalache model checker. The definitions  *)
(* of `clean` are reproduced here so that this module is self-contained.   *)
(*                                                                         *)
(* Model configuration:                                                    *)
(*   CONSTANTS DNA = 5, PRIMER = 5                                         *)
(*   INVARIANTS TypeOK, primerPositive, preservationInvariant              *)
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

vars == <<tee, primer, dna, template, hybrid>>

natMin(i, j) == IF i < j THEN i ELSE j

(***************************************************************************)
(* Heating separates double-stranded DNA and hybrids into templates and    *)
(* primers.                                                                *)
(***************************************************************************)
heat ==
    /\ tee = "Hot"
    /\ tee' = "TooHot"
    /\ primer' = primer + hybrid
    /\ dna' = 0
    /\ template' = template + hybrid + 2 * dna
    /\ hybrid' = 0

(***************************************************************************)
(* Cooling brings the mixture back to the working temperature.             *)
(***************************************************************************)
cool ==
    /\ tee = "TooHot"
    /\ tee' = "Hot"
    /\ UNCHANGED <<primer, dna, template, hybrid>>

(***************************************************************************)
(* Annealing: some primers bind to templates, forming hybrids.             *)
(***************************************************************************)
anneal ==
    /\ tee = "Hot"
    /\ UNCHANGED tee
    /\ \E k \in 1..natMin(primer, template) :
          /\ primer' = primer - k
          /\ template' = template - k
          /\ hybrid' = hybrid + k
          /\ UNCHANGED dna

(***************************************************************************)
(* Extension: hybrids are extended into double-stranded DNA.               *)
(***************************************************************************)
extend ==
    /\ tee = "Hot"
    /\ UNCHANGED tee
    /\ dna' = dna + hybrid
    /\ hybrid' = 0
    /\ UNCHANGED <<primer, template>>

Init ==
    /\ tee = "Hot"
    /\ primer = PRIMER
    /\ dna = DNA
    /\ template = 0
    /\ hybrid = 0

Next ==
    \/ anneal
    \/ extend
    \/ heat
    \/ cool

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)
TypeOK ==
    /\ tee \in {"Hot", "TooHot"}
    /\ primer \in Nat
    /\ dna \in Nat
    /\ template \in Nat
    /\ hybrid \in Nat

primerPositive == primer >= 0

preservationInvariant ==
    template + primer + 2 * (dna + hybrid) = PRIMER + 2 * DNA

=============================================================================