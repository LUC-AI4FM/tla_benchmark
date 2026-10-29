--------------------------- MODULE APAclean ---------------------------
(***************************************************************************)
(* Apalache annotation wrapper for the PCR specification "clean".          *)
(* It adds type annotations in comments for the constants and variables,   *)
(* so the original specification can stay free of tool annotations.       *)
(* The definitions of the "clean" module are inlined here so that this     *)
(* module is self-contained and binds to the model-checking configuration. *)
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

vars == << tee, primer, dna, template, hybrid >>

natMin(i, j) == IF i < j THEN i ELSE j

TypeOK == /\ tee \in {"Hot", "Cool"}
          /\ primer \in Nat
          /\ dna \in Nat
          /\ template \in Nat
          /\ hybrid \in Nat

Init == /\ tee = "Hot"
        /\ primer = PRIMER
        /\ dna = DNA
        /\ template = 0
        /\ hybrid = 0

heat == /\ tee = "Cool"
        /\ tee' = "Hot"
        /\ primer' = primer + hybrid
        /\ template' = template + hybrid + 2 * dna
        /\ dna' = 0
        /\ hybrid' = 0

cool == /\ tee = "Hot"
        /\ tee' = "Cool"
        /\ UNCHANGED << primer, dna, template, hybrid >>

anneal == /\ tee = "Cool"
          /\ \E k \in 1..natMin(primer, template) :
                /\ primer' = primer - k
                /\ template' = template - k
                /\ hybrid' = hybrid + k
          /\ UNCHANGED << tee, dna >>

extend == /\ tee = "Cool"
          /\ \E k \in 1..hybrid :
                /\ hybrid' = hybrid - k
                /\ dna' = dna + k
          /\ UNCHANGED << tee, primer, template >>

Next == heat \/ cool \/ anneal \/ extend

Spec == Init /\ [][Next]_vars

primerPositive == primer >= 0

preservationInvariant ==
    template + primer + 2 * (dna + hybrid) = PRIMER + 2 * DNA

=============================================================================