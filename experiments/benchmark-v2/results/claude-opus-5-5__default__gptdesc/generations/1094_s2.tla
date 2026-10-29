------------------------------- MODULE stages -------------------------------
(***************************************************************************)
(* A simplified model of the Polymerase Chain Reaction (PCR) with          *)
(* explicit thermal stages and molecular counts.                           *)
(*                                                                         *)
(*   tee      : current temperature of the thermocycler ("Hot"/"Cold")     *)
(*   primer   : number of free primers remaining                           *)
(*   dna      : number of double-stranded DNA molecules                    *)
(*   template : number of single-stranded template molecules               *)
(*   hybrid   : number of template-primer hybrids                          *)
(*   stage    : stage / history variable constraining action order         *)
(*   cycle    : number of completed PCR cycles                             *)
(*                                                                         *)
(* The stage variable forces the sequence                                  *)
(*   heat (denature) -> cool -> anneal -> extend -> heat -> ...            *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS DNA,      \* initial number of double-stranded DNA molecules
          PRIMER    \* initial number of primers

ASSUME /\ DNA \in Nat
       /\ PRIMER \in Nat

VARIABLES tee, primer, dna, template, hybrid, stage, cycle

vars == << tee, primer, dna, template, hybrid, stage, cycle >>

Stages == {"init", "denatured", "cooled", "annealed", "extended"}

natMin(i, j) == IF i < j THEN i ELSE j

-----------------------------------------------------------------------------
TypeOK ==
    /\ tee      \in {"Hot", "Cold"}
    /\ primer   \in Nat
    /\ dna      \in Nat
    /\ template \in Nat
    /\ hybrid   \in Nat
    /\ stage    \in Stages
    /\ cycle    \in Nat

-----------------------------------------------------------------------------
Init ==
    /\ tee      = "Hot"
    /\ primer   = PRIMER
    /\ dna      = DNA
    /\ template = 0
    /\ hybrid   = 0
    /\ stage    = "init"
    /\ cycle    = 0

(***************************************************************************)
(* Heating: denaturation. Every double strand separates into two single   *)
(* stranded templates. Allowed initially or after an extension step.      *)
(***************************************************************************)
heat ==
    /\ stage \in {"init", "extended"}
    /\ tee'      = "Hot"
    /\ template' = template + 2 * dna
    /\ dna'      = 0
    /\ stage'    = "denatured"
    /\ UNCHANGED << primer, hybrid, cycle >>

(***************************************************************************)
(* Cooling: the temperature drops so that primers can anneal.             *)
(***************************************************************************)
cool ==
    /\ stage = "denatured"
    /\ tee   = "Hot"
    /\ tee'   = "Cold"
    /\ stage' = "cooled"
    /\ UNCHANGED << primer, dna, template, hybrid, cycle >>

(***************************************************************************)
(* Annealing: primers bind to single-stranded templates, forming hybrids. *)
(***************************************************************************)
anneal ==
    /\ stage = "cooled"
    /\ tee   = "Cold"
    /\ LET k == natMin(primer, template)
       IN  /\ primer'   = primer - k
           /\ template' = template - k
           /\ hybrid'   = hybrid + k
    /\ stage' = "annealed"
    /\ UNCHANGED << tee, dna, cycle >>

(***************************************************************************)
(* Extension: polymerase extends each hybrid into a double strand.        *)
(* Completes one PCR cycle.                                                *)
(***************************************************************************)
extend ==
    /\ stage = "annealed"
    /\ dna'    = dna + hybrid
    /\ hybrid' = 0
    /\ stage'  = "extended"
    /\ cycle'  = cycle + 1
    /\ UNCHANGED << tee, primer, template >>

Next == heat \/ cool \/ anneal \/ extend

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(heat)
    /\ WF_vars(cool)
    /\ WF_vars(anneal)
    /\ WF_vars(extend)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties imported from the instantiated clean (abstract) module.     *)
(***************************************************************************)
cleanInstance == INSTANCE clean

cleanSpec      == cleanInstance!Spec
cleanTypeOK    == cleanInstance!TypeOK
primerDepleted == cleanInstance!primerDepleted

THEOREM Spec => []TypeOK
THEOREM Spec => cleanSpec
=============================================================================