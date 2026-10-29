---------------------------- MODULE PCR ----------------------------
(***************************************************************************)
(* A very abstract model of the Polymerase Chain Reaction (PCR) cycle.     *)
(*                                                                         *)
(* State:                                                                  *)
(*   tee      - the temperature of the reaction ("Hot" or "TooHot")        *)
(*   primer   - number of free primers                                     *)
(*   dna      - number of double-stranded DNA molecules                    *)
(*   template - number of single-stranded templates                        *)
(*   hybrid   - number of template-primer hybrids                          *)
(*                                                                         *)
(* The reaction alternates among heating (denaturation), cooling,          *)
(* annealing (a primer binds to a template, forming a hybrid), and         *)
(* extension (a hybrid is extended into a double-stranded DNA).            *)
(*                                                                         *)
(* Many biochemical details are deliberately omitted (nucleotides,         *)
(* polymerase, strand directionality, imperfect yields, and so on).        *)
(* PCR is treated as a coarse state-transition system over counts.         *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS DNA,      \* initial number of double-stranded DNA molecules
          PRIMER    \* initial number of primers

ASSUME DNA \in Nat /\ PRIMER \in Nat

VARIABLES tee, primer, dna, template, hybrid

vars == << tee, primer, dna, template, hybrid >>

Temperatures == {"Hot", "TooHot"}

natMin(i, j) == IF i < j THEN i ELSE j

-----------------------------------------------------------------------------

Init == /\ tee      = "Hot"
        /\ primer   = PRIMER
        /\ dna      = DNA
        /\ template = 0
        /\ hybrid   = 0

(***************************************************************************)
(* Heating (denaturation): every double-stranded DNA separates into two    *)
(* single-stranded templates, and every hybrid separates into a template   *)
(* and a free primer.                                                      *)
(***************************************************************************)
heat == /\ tee = "Hot"
        /\ tee'      = "TooHot"
        /\ primer'   = primer + hybrid
        /\ dna'      = 0
        /\ template' = template + hybrid + 2 * dna
        /\ hybrid'   = 0

(***************************************************************************)
(* Cooling: the reaction returns to the working temperature.               *)
(***************************************************************************)
cool == /\ tee = "TooHot"
        /\ tee' = "Hot"
        /\ UNCHANGED << primer, dna, template, hybrid >>

(***************************************************************************)
(* Annealing: some nondeterministic number k of available primers bind to *)
(* k available templates, forming k hybrids.                               *)
(***************************************************************************)
anneal == /\ tee = "Hot"
          /\ UNCHANGED << tee, dna >>
          /\ \E k \in 1..natMin(primer, template) :
                /\ primer'   = primer - k
                /\ template' = template - k
                /\ hybrid'   = hybrid + k

(***************************************************************************)
(* Extension: every hybrid is extended into a double-stranded DNA.         *)
(***************************************************************************)
extend == /\ tee = "Hot"
          /\ hybrid > 0
          /\ UNCHANGED << tee, primer, template >>
          /\ dna'    = dna + hybrid
          /\ hybrid' = 0

Next == heat \/ cool \/ anneal \/ extend

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

TypeOK == /\ tee      \in Temperatures
          /\ primer   \in Nat
          /\ dna      \in Nat
          /\ template \in Nat
          /\ hybrid   \in Nat

NonNegative == /\ primer   >= 0
               /\ dna      >= 0
               /\ template >= 0
               /\ hybrid   >= 0

(***************************************************************************)
(* Count preservation: each double-stranded DNA and each hybrid account    *)
(* for two units (two strands, or a template plus a primer), while each    *)
(* free primer and each free template account for one unit.                *)
(***************************************************************************)
Constant ==
    primer + 2 * dna + template + 2 * hybrid = PRIMER + 2 * DNA

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness property: eventually all primers are consumed.                 *)
(*                                                                         *)
(* NOTE: This property does NOT hold. For example, heating can repeatedly  *)
(* release primers from hybrids before extension occurs, the system can    *)
(* cycle heat/cool forever, and annealing may consume fewer primers than   *)
(* are available. Weak fairness on Next does not rule these out.          *)
(***************************************************************************)
primerDepleted == <>(primer = 0)

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ NonNegative /\ Constant)
=============================================================================