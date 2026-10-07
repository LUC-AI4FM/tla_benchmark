------------------------------ MODULE LockHS ------------------------------
EXTENDS Lock, Stuttering, Peterson

CONSTANTS pc_translation, c_translation

VARIABLES pc, flag, turn, h_turn, s

(* ------------------------------------------------------------------ *)
(* Initial condition:  base lock init + history and stutter init      *)
InitHS == Init /\ h_turn = 1 /\ s = top

(* ------------------------------------------------------------------ *)
(* Auxiliary action that wraps the base l1 step with two stuttering   *)
(* steps.  The history variable is updated only during the appropriate*)
(* stutter transition.                                                *)
l1HS ==
  PostStutter(l1) /\
  (h_turn' = IF pc' = 1 THEN 1 ELSE h_turn)

(* ------------------------------------------------------------------ *)
(* All other actions proceed without stuttering and leave h_turn      *)
(* unchanged.                                                         *)
NextHS == l0 \/ cs \/ l2 \/ l1HS

(* ------------------------------------------------------------------ *)
(* Temporal specification of the augmented lock                       *)
SpecHS == InitHS /\ [][NextHS]_<<pc, flag, turn, h_turn, s>>

(* ------------------------------------------------------------------ *)
(* Type correctness invariant                                         *)
TypeOKHS ==
  /\ pc   \in Proc
  /\ flag \in [Proc -> BOOLEAN]
  /\ turn \in Proc
  /\ h_turn \in Proc
  /\ s    \in StutterState

(* ------------------------------------------------------------------ *)
(* Consistency between stuttering state and history variable         *)
InvHS == IF s = top THEN h_turn = 1 ELSE TRUE

(* ------------------------------------------------------------------ *)
(* Mutual exclusion invariant inherited from Lock                     *)
LockInv == LockInv

(* ------------------------------------------------------------------ *)
(* Theorems establishing bidirectional refinement                    *)
THEOREM SpecHS_implies_PSpec == SpecHS => PSpec
THEOREM PSpec_implies_SpecHS == PSpec => SpecHS

=============================================================================