------------------------- MODULE FaultTolerantAtomicCommit -------------------------
(***************************************************************************)
(* An abstract model of a fault-tolerant atomic commit protocol: a        *)
(* coordinator and a fixed set of identical participants.                 *)
(*                                                                         *)
(* The model is two-phase commit with presumed abort and stable storage.  *)
(*                                                                         *)
(* Messages: prepare, vote(yes/no), and the coordinator decisions          *)
(* commit and abort.                                                       *)
(*                                                                         *)
(* Failures:                                                               *)
(*   - The coordinator and the participants can crash and recover.        *)
(*   - Protocol state survives a crash (it is logged to stable storage).  *)
(*   - The coordinator's volatile vote tally is lost on a crash.          *)
(*   - A coordinator that recovers without a logged decision presumes     *)
(*     abort.                                                              *)
(*   - Total crashes are bounded by MaxCrashes (the bounded failure       *)
(*     model).                                                             *)
(*                                                                         *)
(* Network: the network is a set of messages.                             *)
(*   - Messages can be lost at any time.                                   *)
(*   - Messages can be delivered any number of times. Receiving does not  *)
(*     consume a message, so duplication is modeled.                      *)
(*   - Retransmission actions re-insert lost messages.                    *)
(*   - Strong fairness on reception models eventual delivery of messages  *)
(*     that are retransmitted infinitely often.                           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Participants,   \* fixed, symmetric set of participant ids
          MaxCrashes      \* bound on the total number of crash events

ASSUME /\ Participants # {}
       /\ MaxCrashes \in Nat

VARIABLES pState,   \* participant protocol state (stable)
          pVote,    \* vote cast by each participant (stable)
          pUp,      \* participant is running (TRUE) or crashed (FALSE)
          cState,   \* coordinator protocol state / logged decision (stable)
          cVotes,   \* yes-votes received by coordinator (volatile)
          cUp,      \* coordinator is running or crashed
          msgs,     \* the network: set of messages in transit
          crashes   \* number of crash events so far

vars == <<pState, pVote, pUp, cState, cVotes, cUp, msgs, crashes>>

PStates == {"initial", "prepared", "committed", "aborted"}
CStates == {"init", "waiting", "committed", "aborted"}
Votes   == {"none", "yes", "no"}

PrepareMsg == [type |-> "prepare"]
CommitMsg  == [type |-> "commit"]
AbortMsg   == [type |-> "abort"]
VoteMsg(p, v) == [type |-> "vote", src |-> p, vote |-> v]

Messages ==
       {PrepareMsg, CommitMsg, AbortMsg}
  \cup [type : {"vote"}, src : Participants, vote : {"yes", "no"}]

-----------------------------------------------------------------------------
TypeOK ==
  /\ pState  \in [Participants -> PStates]
  /\ pVote   \in [Participants -> Votes]
  /\ pUp     \in [Participants -> BOOLEAN]
  /\ cState  \in CStates
  /\ cVotes  \subseteq Participants
  /\ cUp     \in BOOLEAN
  /\ msgs    \subseteq Messages
  /\ crashes \in 0..MaxCrashes

Init ==
  /\ pState  = [p \in Participants |-> "initial"]
  /\ pVote   = [p \in Participants |-> "none"]
  /\ pUp     = [p \in Participants |-> TRUE]
  /\ cState  = "init"
  /\ cVotes  = {}
  /\ cUp     = TRUE
  /\ msgs    = {}
  /\ crashes = 0

-----------------------------------------------------------------------------
(*************************** Coordinator actions ***************************)

CSendPrepare ==
  /\ cUp /\ cState = "init"
  /\ cState' = "waiting"
  /\ msgs' = msgs \cup {PrepareMsg}
  /\ UNCHANGED <<pState, pVote, pUp, cVotes, cUp, crashes>>

CRetransmitPrepare ==
  /\ cUp /\ cState = "waiting"
  /\ msgs' = msgs \cup {PrepareMsg}
  /\ UNCHANGED <<pState, pVote, pUp, cState, cVotes, cUp, crashes>>

CRcvVote(p) ==
  /\ cUp /\ cState = "waiting"
  /\ \E v \in {"yes", "no"} :
       /\ VoteMsg(p, v) \in msgs
       /\ IF v = "yes"
            THEN /\ cVotes' = cVotes \cup {p}
                 /\ UNCHANGED <<cState, msgs>>
            ELSE /\ cState' = "aborted"
                 /\ msgs' = msgs \cup {AbortMsg}
                 /\ UNCHANGED cVotes
  /\ UNCHANGED <<pState, pVote, pUp, cUp, crashes>>

CDecideCommit ==
  /\ cUp /\ cState = "waiting"
  /\ cVotes = Participants
  /\ cState' = "committed"
  /\ msgs' = msgs \cup {CommitMsg}
  /\ UNCHANGED <<pState, pVote, pUp, cVotes, cUp, crashes>>

\* Nondeterministic timeout. This action is not fair: the coordinator
\* is never forced to abort.
CTimeoutAbort ==
  /\ cUp /\ cState = "waiting"
  /\ cState' = "aborted"
  /\ msgs' = msgs \cup {AbortMsg}
  /\ UNCHANGED <<pState, pVote, pUp, cVotes, cUp, crashes>>

CRetransmitDecision ==
  /\ cUp /\ cState \in {"committed", "aborted"}
  /\ msgs' = msgs \cup {IF cState = "committed" THEN CommitMsg ELSE AbortMsg}
  /\ UNCHANGED <<pState, pVote, pUp, cState, cVotes, cUp, crashes>>

CCrash ==
  /\ cUp /\ crashes < MaxCrashes
  /\ cUp' = FALSE
  /\ cVotes' = {}                       \* volatile state is lost
  /\ crashes' = crashes + 1
  /\ UNCHANGED <<pState, pVote, pUp, cState, msgs>>

\* Recovery with presumed abort: an undecided coordinator aborts.
CRecover ==
  /\ ~cUp
  /\ cUp' = TRUE
  /\ cState' = IF cState \in {"init", "waiting"} THEN "aborted" ELSE cState
  /\ UNCHANGED <<pState, pVote, pUp, cVotes, msgs, crashes>>

-----------------------------------------------------------------------------
(*************************** Participant actions ***************************)

PVoteYes(p) ==
  /\ pUp[p] /\ pState[p] = "initial" /\ PrepareMsg \in msgs
  /\ pState' = [pState EXCEPT ![p] = "prepared"]
  /\ pVote'  = [pVote  EXCEPT ![p] = "yes"]
  /\ msgs'   = msgs \cup {VoteMsg(p, "yes")}
  /\ UNCHANGED <<pUp, cState, cVotes, cUp, crashes>>

PVoteNo(p) ==
  /\ pUp[p] /\ pState[p] = "initial" /\ PrepareMsg \in msgs
  /\ pState' = [pState EXCEPT ![p] = "aborted"]
  /\ pVote'  = [pVote  EXCEPT ![p] = "no"]
  /\ msgs'   = msgs \cup {VoteMsg(p, "no")}
  /\ UNCHANGED <<pUp, cState, cVotes, cUp, crashes>>

PHandlePrepare(p) == PVoteYes(p) \/ PVoteNo(p)

\* A participant that has not voted yes may abort unilaterally.
PUnilateralAbort(p) ==
  /\ pUp[p] /\ pState[p] = "initial"
  /\ pState' = [pState EXCEPT ![p] = "aborted"]
  /\ pVote'  = [pVote  EXCEPT ![p] = "no"]
  /\ UNCHANGED <<pUp, cState, cVotes, cUp, msgs, crashes>>

PResendVote(p) ==
  /\ pUp[p] /\ pVote[p] # "none"
  /\ msgs' = msgs \cup {VoteMsg(p, pVote[p])}
  /\ UNCHANGED <<pState, pVote, pUp, cState, cVotes, cUp, crashes>>

PRcvCommit(p) ==
  /\ pUp[p] /\ pState[p] = "prepared" /\ CommitMsg \in msgs
  /\ pState' = [pState EXCEPT ![p] = "committed"]
  /\ UNCHANGED <<pVote, pUp, cState, cVotes, cUp, msgs, crashes>>

PRcvAbort(p) ==
  /\ pUp[p] /\ pState[p] \in {"initial", "prepared"} /\ AbortMsg \in msgs
  /\ pState' = [pState EXCEPT ![p] = "aborted"]
  /\ UNCHANGED <<pVote, pUp, cState, cVotes, cUp, msgs, crashes>>

PCrash(p) ==
  /\ pUp[p] /\ crashes < MaxCrashes
  /\ pUp' = [pUp EXCEPT ![p] = FALSE]
  /\ crashes' = crashes + 1
  /\ UNCHANGED <<pState, pVote, cState, cVotes, cUp, msgs>>

\* Recovery from stable storage. A prepared participant stays prepared
\* (blocked) until it learns the decision.
PRecover(p) ==
  /\ ~pUp[p]
  /\ pUp' = [pUp EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<pState, pVote, cState, cVotes, cUp, msgs, crashes>>

-----------------------------------------------------------------------------
(******************************* Network ***********************************)

LoseMsg ==
  /\ \E m \in msgs : msgs' = msgs \ {m}
  /\ UNCHANGED <<pState, pVote, pUp, cState, cVotes, cUp, crashes>>

-----------------------------------------------------------------------------
Next ==
  \/ CSendPrepare \/ CRetransmitPrepare \/ CDecideCommit
  \/ CTimeoutAbort \/ CRetransmitDecision \/ CCrash \/ CRecover
  \/ \E p \in Participants :
        \/ CRcvVote(p) \/ PHandlePrepare(p) \/ PUnilateralAbort(p)
        \/ PResendVote(p) \/ PRcvCommit(p) \/ PRcvAbort(p)
        \/ PCrash(p) \/ PRecover(p)
  \/ LoseMsg

(***************************************************************************)
(* Fairness assumptions needed for liveness:                               *)
(*                                                                         *)
(* Weak fairness:                                                          *)
(*   - Recoveries: no process stays crashed forever.                       *)
(*   - Retransmissions: reliable retransmission of lost messages.          *)
(*   - Commit decision.                                                    *)
(*                                                                         *)
(* Strong fairness:                                                        *)
(*   - Message receptions: fair delivery. A message that is sent          *)
(*     infinitely often is eventually received, despite loss.             *)
(*                                                                         *)
(* No fairness:                                                            *)
(*   - Crashes, loss, timeouts and unilateral aborts.                      *)
(***************************************************************************)
Fairness ==
  /\ WF_vars(CSendPrepare)
  /\ WF_vars(CRetransmitPrepare)
  /\ WF_vars(CDecideCommit)
  /\ WF_vars(CRetransmitDecision)
  /\ WF_vars(CRecover)
  /\ \A p \in Participants :
        /\ WF_vars(PRecover(p))
        /\ WF_vars(PResendVote(p))
        /\ SF_vars(CRcvVote(p))
        /\ SF_vars(PHandlePrepare(p))
        /\ SF_vars(PRcvCommit(p))
        /\ SF_vars(PRcvAbort(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(**************************** Safety invariants ****************************)

Decided(p) == pState[p] \in {"committed", "aborted"}

\* Agreement among non-faulty participants (as stated).
AgreementNonFaulty ==
  \A p, q \in Participants :
     (pUp[p] /\ pUp[q]) => ~(pState[p] = "committed" /\ pState[q] = "aborted")

\* Agreement among all participants. This is stronger, and holds because
\* protocol state is kept in stable storage.
Agreement ==
  \A p, q \in Participants :
     ~(pState[p] = "committed" /\ pState[q] = "aborted")

\* Validity (abort part): any no vote forbids commit.
ValidityAbort ==
  (\E p \in Participants : pVote[p] = "no") =>
     /\ cState # "committed"
     /\ \A q \in Participants : pState[q] # "committed"

\* Commit only happens if everyone voted yes.
ValidityCommit ==
  (cState = "committed" \/ \E p \in Participants : pState[p] = "committed")
     => \A q \in Participants : pVote[q] = "yes"

\* Participants are consistent with the coordinator's logged decision.
CoordinatorConsistency ==
  \A p \in Participants :
     /\ pState[p] = "committed" => cState = "committed"
     /\ pState[p] = "aborted" /\ pVote[p] # "no" => cState = "aborted"

\* Decision messages reflect the logged decision.
MessageConsistency ==
  /\ CommitMsg \in msgs => cState = "committed"
  /\ AbortMsg  \in msgs => cState = "aborted"
  /\ ~(CommitMsg \in msgs /\ AbortMsg \in msgs)

\* Non-triviality check for "if all vote commit, commit CAN occur".
\* TLC is EXPECTED to report a violation of this invariant. The
\* counterexample trace witnesses a reachable commit.
CommitUnreachable == cState # "committed"

Safety ==
  /\ TypeOK
  /\ Agreement /\ AgreementNonFaulty
  /\ ValidityAbort /\ ValidityCommit
  /\ CoordinatorConsistency /\ MessageConsistency

(********************** Integrity (action properties) **********************)

Integrity ==
  [][ \A p \in Participants :
        /\ pState[p] = "committed" => pState'[p] = "committed"
        /\ pState[p] = "aborted"   => pState'[p] = "aborted" ]_vars

CoordinatorIntegrity ==
  [][ /\ cState = "committed" => cState' = "committed"
      /\ cState = "aborted"   => cState' = "aborted" ]_vars

VoteIntegrity ==
  [][ \A p \in Participants :
        pVote[p] # "none" => pVote'[p] = pVote[p] ]_vars

(************************** Liveness properties ****************************)

CoordinatorDecided == cState \in {"committed", "aborted"}
AllDecided         == \A p \in Participants : Decided(p)

\* Weak termination guarantee. Suppose that:
\*   - the coordinator does not stay crashed forever, and
\*   - all participants eventually stay up, so non-faulty ones respond.
\* Then a decision is eventually reached and learned by all participants.
\* Under Spec this premise follows from bounded crashes plus fair recovery.
Termination ==
  ((<>[]cUp) /\ (\A p \in Participants : <>[]pUp[p]))
     => <>(CoordinatorDecided /\ AllDecided)

EventuallyDecision == <>CoordinatorDecided
EventuallyAllDecide == <>[]AllDecided

(***************************************************************************)
(* Symmetry reduction.                                                     *)
(*                                                                         *)
(* Participants are identical, so their ids may be permuted. Declare in   *)
(* the TLC config:                                                         *)
(*   SYMMETRY Symmetry                                                     *)
(* with Participants given as a set of model values.                      *)
(*                                                                         *)
(* Use symmetry only when checking invariants and action properties.      *)
(* For temporal (liveness) properties, run TLC without SYMMETRY: symmetry *)
(* reduction can make liveness checking unsound.                          *)
(*                                                                         *)
(* Suggested TLC config:                                                   *)
(*   - Participants = {p1,p2,p3}, MaxCrashes = 2                           *)
(*   - INVARIANTS Safety                                                   *)
(*   - PROPERTIES Integrity CoordinatorIntegrity VoteIntegrity             *)
(*                Termination EventuallyDecision EventuallyAllDecide       *)
(***************************************************************************)
Symmetry == Permutations(Participants)

THEOREM Spec => []Safety
THEOREM Spec => Integrity /\ CoordinatorIntegrity /\ VoteIntegrity
THEOREM Spec => Termination /\ EventuallyDecision /\ EventuallyAllDecide
=============================================================================