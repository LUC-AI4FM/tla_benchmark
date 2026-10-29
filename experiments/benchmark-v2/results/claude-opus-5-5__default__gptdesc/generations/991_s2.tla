------------------------------ MODULE ACP_SB_TLC ------------------------------
(***************************************************************************)
(* TLC-oriented wrapper around the ACP_SB (Atomic Commitment Protocol,     *)
(* simple broadcast) specification.  The CONSTANTS (participants, commit,  *)
(* abort, ...), VARIABLES (participant, coordinator, ...), Init, Next,     *)
(* Spec, fairness conditions and the original invariants are all          *)
(* inherited from ACP_SB via EXTENDS.                                      *)
(***************************************************************************)
EXTENDS ACP_SB, TLC

(***************************************************************************)
(* Re-export of the underlying protocol's initial predicate, next-state    *)
(* relation and complete specification (including its fairness            *)
(* conditions), for use in TLC configuration files.                        *)
(***************************************************************************)
TLCInit == Init

TLCNext == Next

TLCSpec == Spec

(***************************************************************************)
(* Symmetry set: all permutations of the participants.                     *)
(***************************************************************************)
Perms == Permutations(participants)

(***************************************************************************)
(* AC4 rewritten as an explicit stuttering-invariant temporal formula      *)
(* over the participant variable: once a participant has decided commit   *)
(* (respectively abort), it never changes that decision.                   *)
(***************************************************************************)
AC4_alt ==
    [][ /\ \A i \in participants :
              participant[i].decision = commit
                  => participant'[i].decision = commit
        /\ \A j \in participants :
              participant[j].decision = abort
                  => participant'[j].decision = abort
      ]_<<participant>>

(***************************************************************************)
(* Liveness: every participant eventually reaches either the commit or     *)
(* the abort decision state.                                               *)
(***************************************************************************)
AllDecide ==
    \A i \in participants :
        <>(participant[i].decision \in {commit, abort})

(***************************************************************************)
(* Properties to be checked by TLC.                                        *)
(***************************************************************************)
THEOREM TLCSpec => AC4_alt
THEOREM TLCSpec => AllDecide

================================================================================