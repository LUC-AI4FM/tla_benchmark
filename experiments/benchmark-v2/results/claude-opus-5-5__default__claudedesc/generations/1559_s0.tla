------------------------------- MODULE LockHS -------------------------------
(***************************************************************************)
(* LockHS augments the simple mutual-exclusion specification Lock with two  *)
(* auxiliary variables:                                                     *)
(*                                                                          *)
(*   h_turn : a history variable recording which process was assigned the   *)
(*            Peterson "turn" value.                                         *)
(*   s      : a stuttering variable, from module Stuttering.                 *)
(*                                                                          *)
(* Together they let LockHS simulate the three atomic steps that Peterson's *)
(* algorithm uses to enter its critical section. Lock collapses those steps *)
(* into the single step l1. Under a refinement mapping, LockHS implements    *)
(* Peterson's algorithm, and it also implements Lock.                        *)
(*                                                                          *)
(* This module assumes that module Lock defines:                            *)
(*   - the variables pc and c, and the tuple vars == <<pc, c>>;              *)
(*   - Other, Init, l0, l1, cs, l2, Spec, TypeOK and LockInv.               *)
(* It also assumes that module Stuttering defines top and PostStutter.      *)
(***************************************************************************)
EXTENDS Lock

VARIABLES h_turn, s

varsHS == <<vars, h_turn, s>>

(***************************************************************************)
(* The stuttering module. Its "vars" parameter is the tuple of base Lock    *)
(* variables, which must stay unchanged during the inserted stutter steps.  *)
(***************************************************************************)
INSTANCE Stuttering WITH vars <- vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Initial condition                                                        *)
(***************************************************************************)
InitHS == /\ Init
          /\ h_turn = 1
          /\ s = top

-----------------------------------------------------------------------------
(***************************************************************************)
(* Actions                                                                  *)
(***************************************************************************)

\* l0 takes no stutter steps and leaves h_turn unchanged.
l0HS(self) == /\ s = top
              /\ l0(self)
              /\ UNCHANGED <<h_turn, s>>

(***************************************************************************)
(* l1 is followed by two inserted stutter steps, so that it corresponds to  *)
(* Peterson's three atomic entry steps:                                     *)
(*   1. the real l1 step         -> Peterson sets flag[self] (s.val := 2)   *)
(*   2. first stutter (val 2->1) -> Peterson sets turn to Other(self)       *)
(*   3. second stutter (val 1->top) -> Peterson tests and enters cs         *)
(* h_turn changes only on the first stutter transition.                     *)
(***************************************************************************)
l1HS(self) == /\ PostStutter(l1(self), "l1", self, 1, 2, LAMBDA j : j - 1)
              /\ h_turn' = IF s # top /\ s.val = 2
                             THEN Other(self)
                             ELSE h_turn

\* cs takes no stutter steps and leaves h_turn unchanged.
csHS(self) == /\ s = top
              /\ cs(self)
              /\ UNCHANGED <<h_turn, s>>

\* l2 takes no stutter steps and leaves h_turn unchanged.
l2HS(self) == /\ s = top
              /\ l2(self)
              /\ UNCHANGED <<h_turn, s>>

procHS(self) == l0HS(self) \/ l1HS(self) \/ csHS(self) \/ l2HS(self)

NextHS == \E self \in {0, 1} : procHS(self)

\* The specification is a safety property only; it has no fairness conditions.
SpecHS == InitHS /\ [][NextHS]_varsHS

-----------------------------------------------------------------------------
(***************************************************************************)
(* Invariants                                                               *)
(***************************************************************************)
TypeOKHS == /\ TypeOK
            /\ h_turn \in {0, 1}
            /\ \/ s = top
               \/ /\ s \in [id : {"l1"}, ctxt : {0, 1}, val : {1, 2}]

(***************************************************************************)
(* Consistency between the stuttering state, the program counters and      *)
(* h_turn. While the l1 stutter steps are pending, the stuttering process   *)
(* is already in cs in Lock. After the first stutter step (s.val = 1),      *)
(* h_turn records the turn that process handed to the other process.        *)
(***************************************************************************)
InvHS == /\ s # top => /\ s.id = "l1"
                       /\ s.ctxt \in {0, 1}
                       /\ s.val \in {1, 2}
                       /\ pc[s.ctxt] = "cs"
         /\ (s # top /\ s.val = 1) => h_turn = Other(s.ctxt)

\* LockInv, the mutual-exclusion invariant, is inherited from module Lock.

-----------------------------------------------------------------------------
(***************************************************************************)
(* Refinement mapping to Peterson's algorithm                               *)
(*                                                                          *)
(* Peterson's labels used here:                                             *)
(*   "a0" noncritical, "a1" set flag, "a2" set turn, "a3a" test,            *)
(*   "cs" critical section, "a4" reset flag.                                *)
(***************************************************************************)
pc_translation ==
  [p \in {0, 1} |->
     CASE pc[p] = "l0" -> "a0"
       [] pc[p] = "l1" -> "a1"
       [] pc[p] = "cs" -> IF s # top /\ s.ctxt = p
                            THEN IF s.val = 2 THEN "a2" ELSE "a3a"
                            ELSE "cs"
       [] pc[p] = "l2" -> "a4"]

c_translation == [p \in {0, 1} |-> c[p]]

P == INSTANCE Peterson WITH pc <- pc_translation,
                            c <- c_translation,
                            turn <- h_turn

PSpec == P!Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* Theorems checked by TLC                                                  *)
(***************************************************************************)
THEOREM SpecHS => [](TypeOKHS /\ InvHS /\ LockInv)

\* LockHS implements Lock: hiding h_turn and s gives back Lock's spec.
THEOREM SpecHS => Spec

\* LockHS implements Peterson under the refinement mapping above.
THEOREM SpecHS => PSpec
=============================================================================