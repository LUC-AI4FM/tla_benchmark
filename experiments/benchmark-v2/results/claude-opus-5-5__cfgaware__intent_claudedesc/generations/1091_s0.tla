-------------------------------- MODULE pcr --------------------------------
(***************************************************************************)
(* An abstract model of the Polymerase Chain Reaction (PCR).               *)
(*                                                                         *)
(*   dna      : number of double-stranded DNA molecules                    *)
(*   template : number of single-stranded templates                        *)
(*   primer   : number of free primers                                     *)
(*   hybrid   : number of template-primer hybrids                          *)
(*   tee      : current temperature state                                  *)
(*                                                                         *)
(* Temperature cycle:                                                      *)
(*   "Hot"    (moderate, ready)  --heat-->   "TooHot" (denaturation)       *)
(*   "TooHot"                    --cool-->   "Hot"    (ready to anneal)    *)
(*   "Hot"                       --anneal--> "Warm"   (annealing done)     *)
(*   "Warm"                      --extend--> "Hot"    (extension done)     *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS DNA, PRIMER

ASSUME /\ DNA \in Nat
       /\ PRIMER \in Nat

VARIABLES tee, primer, dna, template, hybrid

vars == << tee, primer, dna, template, hybrid >>

Temps == {"Hot", "TooHot", "Warm"}

TypeOK ==
    /\ tee \in Temps
    /\ primer \in Nat
    /\ dna \in Nat
    /\ template \in Nat
    /\ hybrid \in Nat

Min(a, b) == IF a <= b THEN a ELSE b

Init ==
    /\ tee = "Hot"
    /\ primer = PRIMER
    /\ dna = DNA
    /\ template = 0
    /\ hybrid = 0

(* High heat: double strands and hybrids denature into single-stranded   *)
(* templates; primers bound in hybrids are released.                      *)
heat ==
    /\ tee = "Hot"
    /\ tee' = "TooHot"
    /\ primer' = primer + hybrid
    /\ dna' = 0
    /\ template' = template + hybrid + 2 * dna
    /\ hybrid' = 0

(* Cooling returns the system to a state ready for annealing.            *)
cool ==
    /\ tee = "TooHot"
    /\ tee' = "Hot"
    /\ UNCHANGED << primer, dna, template, hybrid >>

(* Warm temperature: some nondeterministic number of primers anneal to   *)
(* templates, forming hybrids.                                            *)
anneal ==
    /\ tee = "Hot"
    /\ tee' = "Warm"
    /\ \E k \in 1..Min(primer, template) :
          /\ primer' = primer - k
          /\ template' = template - k
          /\ hybrid' = hybrid + k
    /\ UNCHANGED dna

(* Medium heat: polymerase extends all hybrids into double-stranded DNA. *)
extend ==
    /\ tee = "Warm"
    /\ tee' = "Hot"
    /\ dna' = dna + hybrid
    /\ hybrid' = 0
    /\ UNCHANGED << primer, template >>

Next == heat \/ cool \/ anneal \/ extend

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
primerPositive == primer >= 0

Total == primer + template + 2 * dna + 2 * hybrid

preservationInvariant == Total = PRIMER + 2 * DNA

preservationProperty ==
    [][ primer' + template' + 2 * dna' + 2 * hybrid'
          = primer + template + 2 * dna + 2 * hybrid ]_vars

THEOREM Spec => [](TypeOK /\ primerPositive /\ preservationInvariant)
THEOREM Spec => preservationProperty
=============================================================================