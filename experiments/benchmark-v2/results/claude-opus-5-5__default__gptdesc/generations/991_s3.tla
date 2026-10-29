------------------------------ MODULE MC_ACP_SB ------------------------------
(***************************************************************************)
(* TLC-oriented wrapper around the ACP_SB specification.                   *)
(* The underlying protocol module supplies the constants (participants,    *)
(* yes, no, undecided, commit, abort, ...), the variables (participant,    *)
(* coordinator) and Init, Next and Spec.                                   *)
(***************************************************************************)
EXTENDS ACP_SB, TLC

(***************************************************************************)
(* Symmetry helper: all permutations of the set of participants.           *)
(***************************************************************************)
SymmetryPerms == Permutations(participants)

(***************************************************************************)
(* Initial predicate, next-state relation and specification used for model *)
(* checking. They are the ones of the underlying protocol.                 *)
(***************************************************************************)
MCInit == Init

MCNext == Next

MCSpec == Spec

(***************************************************************************)
(* AC4 rewritten as an explicit stuttering-invariant temporal formula over *)
(* the participant variable: once a participant has decided commit (resp.  *)
(* abort), it keeps that decision in every subsequent step.                *)
(***************************************************************************)
AC4_alt ==
  [][ \A i \in participants :
        /\ (participant[i].decision = commit => participant'[i].decision = commit)
        /\ (participant[i].decision = abort  => participant'[i].decision = abort)
    ]_participant

(***************************************************************************)
(* Liveness-style property: every participant eventually reaches either    *)
(* the commit or the abort decision state.                                 *)
(***************************************************************************)
AllDecide ==
  \A i \in participants :
     <>(participant[i].decision \in {commit, abort})

=============================================================================