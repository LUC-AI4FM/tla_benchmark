------------------------------- MODULE PCR -------------------------------
(***************************************************************************)
(* A very abstract model of the Polymerase Chain Reaction (PCR) cycle.     *)
(*                                                                         *)
(* The state tracks:                                                       *)
(*   tee      - the current "temperature" / stage of the thermal cycle     *)
(*   primer   - number of free primers                                     *)
(*   dna      - number of double-stranded DNA molecules                    *)
(*   template - number of single-stranded templates                        *)
(*   hybrid   - number of template-primer hybrids                          *)
(*                                                                         *)
(* The cycle is: heat (denature) -> cool -> anneal -> extend -> heat ...   *)
(*   - heat:   double-stranded DNA splits into two single-stranded         *)
(*             templates; unextended hybrids fall apart into a template    *)
(*             and a primer.                                               *)
(*   - cool:   the mixture is brought down to annealing temperature.       *)
(*   - anneal: some (nondeterministically chosen) number of primers bind   *)
(*             to available templates forming hybrids.                     *)
(*   - extend: polymerase extends each hybrid into double-stranded DNA.    *)
(*                                                                         *)
(* Many biochemical details (nucleotides, polymerase, errors, product      *)
(* lengths, etc.) are intentionally omitted: PCR is treated as a coarse    *)
(* state-transition system.                                                *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS DNA,     \* initial number of double-stranded DNA molecules
          PRIMER   \* initial number of primers

ASSUME /\ DNA \in Nat
       /\ PRIMER \in Nat

VARIABLES tee, primer, dna, template, hybrid

vars == <<tee, primer, dna, template, hybrid>>

Temps == {"Hot", "Cool", "Annealed", "Extended"}

natMin(i, j) == IF i < j THEN i ELSE j

(***************************************************************************)
(* Initial state: only double-stranded DNA and free primers, at the       *)
(* "Extended" stage so that the first step is heating.                     *)
(***************************************************************************)
Init == /\ tee = "Extended"
        /\ primer = PRIMER
        /\ dna = DNA
        /\ template = 0
        /\ hybrid = 0

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
heat == /\ tee \in {"Annealed", "Extended"}
        /\ tee' = "Hot"
        /\ dna' = 0
        /\ template' = template + hybrid + 2 * dna
        /\ primer' = primer + hybrid
        /\ hybrid' = 0

cool == /\ tee = "Hot"
        /\ tee' = "Cool"
        /\ UNCHANGED <<primer, dna, template, hybrid>>

anneal == /\ tee = "Cool"
          /\ tee' = "Annealed"
          /\ \E k \in 0..natMin(primer, template) :
                /\ primer' = primer - k
                /\ template' = template - k
                /\ hybrid' = hybrid + k
          /\ UNCHANGED dna

extend == /\ tee = "Annealed"
          /\ tee' = "Extended"
          /\ dna' = dna + hybrid
          /\ hybrid' = 0
          /\ UNCHANGED <<primer, template>>

Next == \/ heat
        \/ cool
        \/ anneal
        \/ extend

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(Next)

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
TypeOK == /\ tee \in Temps
          /\ primer \in Nat
          /\ dna \in Nat
          /\ template \in Nat
          /\ hybrid \in Nat

NonNegative == /\ primer >= 0
               /\ dna >= 0
               /\ template >= 0
               /\ hybrid >= 0

(* Each primer and each template strand is counted exactly once: a hybrid *)
(* holds one template and one primer, and a double-stranded DNA molecule  *)
(* holds two strands.                                                      *)
PreservationInvariant ==
    primer + template + 2 * (hybrid + dna) = PRIMER + 2 * DNA

(***************************************************************************)
(* Liveness property                                                       *)
(*                                                                         *)
(* Claims that primers are eventually used up.  NOTE: this does NOT hold:  *)
(* annealing may nondeterministically bind zero primers forever (and with  *)
(* DNA = 0 no template is ever available), so primer can stay positive    *)
(* in every state of an infinite behavior.                                 *)
(***************************************************************************)
PrimersDepleted == <>(primer = 0)

THEOREM Spec => [](TypeOK /\ NonNegative /\ PreservationInvariant)

==========================================================================