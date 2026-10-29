------------------------------ MODULE AtomicCommit ------------------------------
(***************************************************************************)
(* Atomic commitment protocol.                                             *)
(*                                                                         *)
(* A set of interchangeable participants each vote on whether they are     *)
(* prepared to commit a transaction. Each participant then decides         *)
(* "commit" or "abort". The protocol guarantees:                           *)
(*   - Agreement: no participant commits while another aborts.             *)
(*   - Validity: a commit happens only if every participant voted "yes".   *)
(*     Abort is always a permissible outcome (safety valve).               *)
(*   - Stability: decisions are irrevocable.                               *)
(*   - Termination: under weak fairness, every participant decides.        *)
(***************************************************************************)
EXTENDS FiniteSets, TLC

CONSTANT Participant          \* The set of participants

ASSUME Participant # {}

VARIABLES
    vote,       \* vote[p]     \in {"none", "yes", "no"}
    decision    \* decision[p] \in {"undecided", "commit", "abort"}

vars == <<vote, decision>>

VoteVal     == {"none", "yes", "no"}
DecisionVal == {"undecided", "commit", "abort"}

TypeOK ==
    /\ vote     \in [Participant -> VoteVal]
    /\ decision \in [Participant -> DecisionVal]

-----------------------------------------------------------------------------
(* Initial state: nobody has voted and nobody has decided. *)
Init ==
    /\ vote     = [p \in Participant |-> "none"]
    /\ decision = [p \in Participant |-> "undecided"]

(* Participant p casts its vote; votes are cast once and never changed. *)
VoteYes(p) ==
    /\ vote[p] = "none"
    /\ vote' = [vote EXCEPT ![p] = "yes"]
    /\ UNCHANGED decision

VoteNo(p) ==
    /\ vote[p] = "none"
    /\ vote' = [vote EXCEPT ![p] = "no"]
    /\ UNCHANGED decision

(* Participant p decides to commit: only if all participants voted "yes"   *)
(* and no participant has decided to abort.                                *)
DecideCommit(p) ==
    /\ decision[p] = "undecided"
    /\ \A q \in Participant : vote[q] = "yes"
    /\ \A q \in Participant : decision[q] # "abort"
    /\ decision' = [decision EXCEPT ![p] = "commit"]
    /\ UNCHANGED vote

(* Participant p decides to abort: always allowed as long as no            *)
(* participant has already committed.                                      *)
DecideAbort(p) ==
    /\ decision[p] = "undecided"
    /\ \A q \in Participant : decision[q] # "commit"
    /\ decision' = [decision EXCEPT ![p] = "abort"]
    /\ UNCHANGED vote

(* All participants have decided: stutter to avoid spurious deadlock. *)
Terminated ==
    /\ \A p \in Participant : decision[p] # "undecided"
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Participant :
          \/ VoteYes(p)
          \/ VoteNo(p)
          \/ DecideCommit(p)
          \/ DecideAbort(p)
    \/ Terminated

Fairness ==
    \A p \in Participant :
        /\ WF_vars(VoteYes(p) \/ VoteNo(p))
        /\ WF_vars(DecideCommit(p) \/ DecideAbort(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

(* Agreement: no participant commits while another aborts. *)
Agreement ==
    \A p, q \in Participant :
        ~ (decision[p] = "commit" /\ decision[q] = "abort")

(* Validity / justification: a commit requires all participants voted yes. *)
CommitValidity ==
    (\E p \in Participant : decision[p] = "commit")
        => (\A q \in Participant : vote[q] = "yes")

(* Abort is always a valid outcome: aborting is consistent with agreement. *)
AbortValidity ==
    (\E p \in Participant : decision[p] = "abort")
        => (\A q \in Participant : decision[q] # "commit")

Consistency == Agreement /\ CommitValidity /\ AbortValidity

(* Stability: decisions are irrevocable (action form). *)
DecisionStableAction ==
    [][\A p \in Participant :
          decision[p] # "undecided" => decision'[p] = decision[p]]_vars

(* Stability: decisions are irrevocable (temporal form). *)
CommitStable ==
    \A p \in Participant :
        [](decision[p] = "commit" => [](decision[p] = "commit"))

AbortStable ==
    \A p \in Participant :
        [](decision[p] = "abort" => [](decision[p] = "abort"))

Stability == CommitStable /\ AbortStable

(***************************************************************************)
(* Liveness                                                                *)
(***************************************************************************)

(* Termination: every participant eventually reaches a decision. *)
Termination ==
    <>(\A p \in Participant : decision[p] # "undecided")

(***************************************************************************)
(* Model-checking support: participants are interchangeable.               *)
(***************************************************************************)
Symmetry == Permutations(Participant)

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ Consistency)
THEOREM Spec => DecisionStableAction /\ Stability
THEOREM Spec => Termination
=============================================================================