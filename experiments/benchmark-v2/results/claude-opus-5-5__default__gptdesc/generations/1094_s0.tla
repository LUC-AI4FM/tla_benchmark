------------------------------- MODULE stages -------------------------------
(***************************************************************************)
(* A simplified model of the Polymerase Chain Reaction (PCR) with explicit *)
(* thermal stages and molecular counts.                                    *)
(*                                                                         *)
(* The nested module "clean" gives the unconstrained thermal/molecular     *)
(* dynamics. The outer module adds a stage (history) variable and a cycle  *)
(* counter that force the steps into the order heat, cool, anneal,         *)
(* extend. It then imports the clean module's properties through an       *)
(* INSTANCE.                                                               *)
(***************************************************************************)
EXTENDS Naturals

  ------------------------------ MODULE clean ------------------------------
  (*************************************************************************)
  (* Unconstrained ("clean") PCR dynamics.                                 *)
  (*   tee      : current temperature of the reaction                      *)
  (*   primer   : number of free primers                                   *)
  (*   dna      : number of double-stranded DNA molecules                  *)
  (*   template : number of free single-stranded templates                 *)
  (*   hybrid   : number of template-primer hybrids                        *)
  (*************************************************************************)
  CONSTANTS DNA, PRIMER

  VARIABLES tee, primer, dna, template, hybrid

  cvars == <<tee, primer, dna, template, hybrid>>

  Temps == {"Hot", "Cold", "Warm"}

  CMin(a, b) == IF a < b THEN a ELSE b

  TypeOK ==
      /\ tee \in Temps
      /\ primer \in Nat
      /\ dna \in Nat
      /\ template \in Nat
      /\ hybrid \in Nat

  (* Strand conservation: every consumed primer that is not still sitting *)
  (* in an unextended hybrid has become a new DNA strand.                 *)
  Conservation ==
      2 * dna + template + hybrid = 2 * DNA + (PRIMER - primer - hybrid)

  PrimerBound == primer + hybrid <= PRIMER

  Init ==
      /\ tee = "Warm"
      /\ primer = PRIMER
      /\ dna = DNA
      /\ template = 0
      /\ hybrid = 0

  (* Denaturation: double strands separate. Unextended hybrids release *)
  (* their primers.                                                     *)
  Heat ==
      /\ tee # "Hot"
      /\ tee' = "Hot"
      /\ template' = template + hybrid + 2 * dna
      /\ primer' = primer + hybrid
      /\ dna' = 0
      /\ hybrid' = 0

  (* Cooling down to the annealing temperature *)
  Cool ==
      /\ tee = "Hot"
      /\ tee' = "Cold"
      /\ UNCHANGED <<primer, dna, template, hybrid>>

  (* Annealing: primers bind to free templates *)
  Anneal ==
      /\ tee = "Cold"
      /\ LET k == CMin(primer, template)
         IN  /\ primer' = primer - k
             /\ template' = template - k
             /\ hybrid' = hybrid + k
      /\ UNCHANGED <<tee, dna>>

  (* Extension: the polymerase completes hybrids into double strands *)
  Extend ==
      /\ tee = "Cold"
      /\ tee' = "Warm"
      /\ dna' = dna + hybrid
      /\ hybrid' = 0
      /\ UNCHANGED <<primer, template>>

  Next == Heat \/ Cool \/ Anneal \/ Extend

  Spec == Init /\ [][Next]_cvars

  PrimerDepleted == <>(primer = 0)
  ==========================================================================