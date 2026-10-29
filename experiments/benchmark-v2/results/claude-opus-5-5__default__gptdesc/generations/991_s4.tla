------------------------------ MODULE MC_ACP_SB ------------------------------
(***************************************************************************)
(* TLC-oriented wrapper around the ACP_SB specification.                   *)
(* The CONSTANTS, VARIABLES, Init, Next and Spec definitions are inherited *)
(* from ACP_SB, which this module extends.                                 *)
(***************************************************************************)
EXTENDS ACP_SB, TLC

(***************************************************************************)
(* Symmetry helper: all permutations of the set of participants.           *)
(***************************************************************************)
Perms == Permutations(participants)

(***************************************************************************)
(* The specification used for model checking, inherited from ACP_SB.       *)
(***************************************************************************)
MCInit == Init
MCNext == Next
MCSpec == Spec

(***************************************************************************)
(* AC4 restated as an explicit stuttering-invariant temporal formula over  *)
(* the participant variable: once a participant has decided commit (or     *)
(* abort), it never changes that decision.                                 *)
(***************************************************************************)
AC4_alt ==
  [][ /\ \A i \in participants :
           (participant[i].decision = commit => (participant'[i].decision = commit))
      /\ \A j \in participants :
           (participant[j].decision = abort  => (participant'[j].decision = abort))
    ]_<<participant>>

(***************************************************************************)
(* Liveness: every participant eventually decides either commit or abort.  *)
(***************************************************************************)
StrongTermination ==
  \A i \in participants : <>(participant[i].decision \in {commit, abort})

=============================================================================