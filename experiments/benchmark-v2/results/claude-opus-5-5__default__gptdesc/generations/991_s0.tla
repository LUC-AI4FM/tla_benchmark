------------------------------ MODULE ACP_SB_TLC ------------------------------
(***************************************************************************)
(* TLC-oriented wrapper around the ACP_SB specification.                   *)
(*                                                                         *)
(* CONSTANTS, VARIABLES, Init, Next and Spec are inherited from ACP_SB     *)
(* through EXTENDS. This module adds three things:                         *)
(*  - a symmetry helper over permutations of the participants,             *)
(*  - an explicit stuttering-invariant temporal form of AC4,               *)
(*  - a liveness property stating that every participant eventually        *)
(*    decides commit or abort.                                             *)
(***************************************************************************)
EXTENDS ACP_SB, TLC

(***************************************************************************)
(* Symmetry set for TLC: all permutations of the participants.             *)
(***************************************************************************)
Perms == Permutations(participants)

(***************************************************************************)
(* AC4 rewritten as an explicit stuttering-invariant temporal formula      *)
(* over the participant variable. Once a participant has decided commit    *)
(* (resp. abort), it never changes that decision.                          *)
(***************************************************************************)
AC4_alt ==
    [][ \A i \in participants :
          /\ (participant[i].decision = commit
                 => (participant'[i].decision = commit))
          /\ (participant[i].decision = abort
                 => (participant'[i].decision = abort))
      ]_<<participant>>

(***************************************************************************)
(* Liveness: every participant eventually reaches a decision state,        *)
(* either commit or abort.                                                 *)
(***************************************************************************)
AC5 ==
    <>(\A i \in participants : participant[i].decision \in {abort, commit})

(***************************************************************************)
(* Properties to check with TLC under the inherited Spec.                  *)
(***************************************************************************)
THEOREM Spec => AC4_alt
THEOREM Spec => AC5

=============================================================================