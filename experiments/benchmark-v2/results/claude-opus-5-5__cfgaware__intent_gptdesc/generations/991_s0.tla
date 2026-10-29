------------------------------- MODULE AtomicCommit -------------------------------
(***************************************************************************)
(* Fault-tolerant atomic commit with one coordinator and a fixed set of   *)
(* participants. Prepare, vote and decision messages travel over an       *)
(* unreliable network that may lose them. Messages are kept in sets, so   *)
(* resending a message models duplication. The coordinator and the        *)
(* participants may crash and later recover. Their protocol state is      *)
(* kept on stable storage, so it survives a crash. The total number of    *)
(* crashes is bounded by MaxFailures.                                     *)
(*                                                                         *)
(* Liveness relies on these assumptions:                                  *)
(*   - weak fairness on retransmission and recovery;                      *)
(*   - strong fairness on message reception, so a message that is resent  *)
(*     infinitely often is eventually delivered;                          *)
(*   - a bounded number of failures, so every node eventually stays up.   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS participants,   \* the set of identical participants
          waiting,        \* coordinator has not decided yet
          notsent,        \* a vote that has not been sent or received yet
          undecided,      \* a participant that has not decided yet
          commit,         \* commit outcome
          abort,          \* abort outcome
          yes,            \* vote to commit
          no              \* vote to abort

ASSUME participants # {}
ASSUME Cardinality({waiting, notsent, undecided, commit, abort, yes, no}) = 7

MaxFailures == 2          \* bound on the total number of crashes

Votes     == {yes, no}
Decisions == {commit, abort}

VARIABLES
  voteSent,     \* voteSent[p]   \in {notsent, yes, no}       (stable storage)
  pDecision,    \* pDecision[p]  \in {undecided, commit, abort} (stable storage)
  pAlive,       \* pAlive[p]     \in BOOLEAN
  coordState,   \* coordState    \in {waiting, commit, abort}  (stable storage)
  coordVotes,   \* coordVotes[p] \in {notsent, yes, no} : votes received
  coordAlive,   \* coordAlive    \in BOOLEAN
  prepMsgs,     \* prepare messages in transit (one per participant)
  voteMsgs,     \* vote messages in transit: pairs <<p, v>>
  decMsgs,      \* decision messages in transit (broadcast)
  failures      \* number of crashes so far

vars == << voteSent, pDecision, pAlive, coordState, coordVotes, coordAlive,
           prepMsgs, voteMsgs, decMsgs, failures >>

TypeOK ==
  /\ voteSent   \in [participants -> {notsent} \cup Votes]
  /\ pDecision  \in [participants -> {undecided} \cup Decisions]
  /\ pAlive     \in [participants -> BOOLEAN]
  /\ coordState \in {waiting} \cup Decisions
  /\ coordVotes \in [participants -> {notsent} \cup Votes]
  /\ coordAlive \in BOOLEAN
  /\ prepMsgs   \subseteq participants
  /\ voteMsgs   \subseteq (participants \X Votes)
  /\ decMsgs    \subseteq Decisions
  /\ failures   \in 0..MaxFailures

\* Abstract participant phase: initial, prepared, committed or aborted.
PState(p) ==
  IF pDecision[p] = commit THEN "committed"
  ELSE IF pDecision[p] = abort THEN "aborted"
  ELSE IF voteSent[p] = yes THEN "prepared"
  ELSE "initial"

Init ==
  /\ voteSent   = [p \in participants |-> notsent]
  /\ pDecision  = [p \in participants |-> undecided]
  /\ pAlive     = [p \in participants |-> TRUE]
  /\ coordState = waiting
  /\ coordVotes = [p \in participants |-> notsent]
  /\ coordAlive = TRUE
  /\ prepMsgs   = {}
  /\ voteMsgs   = {}
  /\ decMsgs    = {}
  /\ failures   = 0

(***************************** Coordinator ********************************)

\* Send or resend a prepare message until the participant's vote arrives.
CoordSendPrepare(p) ==
  /\ coordAlive
  /\ coordState = waiting
  /\ coordVotes[p] = notsent
  /\ p \notin prepMsgs
  /\ prepMsgs' = prepMsgs \cup {p}
  /\ UNCHANGED << voteSent, pDecision, pAlive, coordState, coordVotes,
                  coordAlive, voteMsgs, decMsgs, failures >>

CoordReceiveVote(p, v) ==
  /\ coordAlive
  /\ <<p, v>> \in voteMsgs
  /\ coordVotes[p] = notsent
  /\ coordVotes' = [coordVotes EXCEPT ![p] = v]
  /\ voteMsgs' = voteMsgs \ {<<p, v>>}
  /\ UNCHANGED << voteSent, pDecision, pAlive, coordState, coordAlive,
                  prepMsgs, decMsgs, failures >>

\* The coordinator commits only if every participant voted yes.
CoordCommit ==
  /\ coordAlive
  /\ coordState = waiting
  /\ \A p \in participants : coordVotes[p] = yes
  /\ coordState' = commit
  /\ decMsgs' = decMsgs \cup {commit}
  /\ UNCHANGED << voteSent, pDecision, pAlive, coordVotes, coordAlive,
                  prepMsgs, voteMsgs, failures >>

\* The coordinator may abort at any time before deciding, for example
\* after a no vote or a timeout.
CoordAbort ==
  /\ coordAlive
  /\ coordState = waiting
  /\ coordState' = abort
  /\ decMsgs' = decMsgs \cup {abort}
  /\ UNCHANGED << voteSent, pDecision, pAlive, coordVotes, coordAlive,
                  prepMsgs, voteMsgs, failures >>

\* Resend the decision. This models reliable retransmission.
CoordResendDecision ==
  /\ coordAlive
  /\ coordState \in Decisions
  /\ coordState \notin decMsgs
  /\ decMsgs' = decMsgs \cup {coordState}
  /\ UNCHANGED << voteSent, pDecision, pAlive, coordState, coordVotes,
                  coordAlive, prepMsgs, voteMsgs, failures >>

CoordCrash ==
  /\ coordAlive
  /\ failures < MaxFailures
  /\ coordAlive' = FALSE
  /\ failures' = failures + 1
  /\ UNCHANGED << voteSent, pDecision, pAlive, coordState, coordVotes,
                  prepMsgs, voteMsgs, decMsgs >>

CoordRecover ==
  /\ ~coordAlive
  /\ coordAlive' = TRUE
  /\ UNCHANGED << voteSent, pDecision, pAlive, coordState, coordVotes,
                  prepMsgs, voteMsgs, decMsgs, failures >>

(***************************** Participants *******************************)

\* Receive a prepare message and vote. A no vote aborts unilaterally.
PVote(p, v) ==
  /\ pAlive[p]
  /\ p \in prepMsgs
  /\ voteSent[p] = notsent
  /\ pDecision[p] = undecided
  /\ voteSent' = [voteSent EXCEPT ![p] = v]
  /\ pDecision' = IF v = no THEN [pDecision EXCEPT ![p] = abort]
                            ELSE pDecision
  /\ prepMsgs' = prepMsgs \ {p}
  /\ voteMsgs' = voteMsgs \cup {<<p, v>>}
  /\ UNCHANGED << pAlive, coordState, coordVotes, coordAlive, decMsgs,
                  failures >>

\* Resend the vote. This models reliable retransmission and duplication.
PResendVote(p) ==
  /\ pAlive[p]
  /\ voteSent[p] \in Votes
  /\ coordVotes[p] = notsent
  /\ <<p, voteSent[p]>> \notin voteMsgs
  /\ voteMsgs' = voteMsgs \cup {<<p, voteSent[p]>>}
  /\ UNCHANGED << voteSent, pDecision, pAlive, coordState, coordVotes,
                  coordAlive, prepMsgs, decMsgs, failures >>

\* Learn the coordinator's decision. The message stays in the set
\* because it is a broadcast.
PReceiveDecision(p, d) ==
  /\ pAlive[p]
  /\ d \in decMsgs
  /\ pDecision[p] = undecided
  /\ pDecision' = [pDecision EXCEPT ![p] = d]
  /\ UNCHANGED << voteSent, pAlive, coordState, coordVotes, coordAlive,
                  prepMsgs, voteMsgs, decMsgs, failures >>

PCrash(p) ==
  /\ pAlive[p]
  /\ failures < MaxFailures
  /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
  /\ failures' = failures + 1
  /\ UNCHANGED << voteSent, pDecision, coordState, coordVotes, coordAlive,
                  prepMsgs, voteMsgs, decMsgs >>

PRecover(p) ==
  /\ ~pAlive[p]
  /\ pAlive' = [pAlive EXCEPT ![p] = TRUE]
  /\ UNCHANGED << voteSent, pDecision, coordState, coordVotes, coordAlive,
                  prepMsgs, voteMsgs, decMsgs, failures >>

(******************************* Network **********************************)

LosePrepare ==
  \E p \in prepMsgs :
    /\ prepMsgs' = prepMsgs \ {p}
    /\ UNCHANGED << voteSent, pDecision, pAlive, coordState, coordVotes,
                    coordAlive, voteMsgs, decMsgs, failures >>

LoseVote ==
  \E m \in voteMsgs :
    /\ voteMsgs' = voteMsgs \ {m}
    /\ UNCHANGED << voteSent, pDecision, pAlive, coordState, coordVotes,
                    coordAlive, prepMsgs, decMsgs, failures >>

LoseDecision ==
  \E d \in decMsgs :
    /\ decMsgs' = decMsgs \ {d}
    /\ UNCHANGED << voteSent, pDecision, pAlive, coordState, coordVotes,
                    coordAlive, prepMsgs, voteMsgs, failures >>

(****************************** Specification *****************************)

Next ==
  \/ \E p \in participants :
       \/ CoordSendPrepare(p)
       \/ PResendVote(p)
       \/ PCrash(p)
       \/ PRecover(p)
       \/ \E v \in Votes : CoordReceiveVote(p, v) \/ PVote(p, v)
       \/ \E d \in Decisions : PReceiveDecision(p, d)
  \/ CoordCommit
  \/ CoordAbort
  \/ CoordResendDecision
  \/ CoordCrash
  \/ CoordRecover
  \/ LosePrepare
  \/ LoseVote
  \/ LoseDecision

Fairness ==
  /\ WF_vars(CoordAbort)
  /\ WF_vars(CoordResendDecision)
  /\ WF_vars(CoordRecover)
  /\ \A p \in participants :
       /\ WF_vars(CoordSendPrepare(p))
       /\ WF_vars(PResendVote(p))
       /\ WF_vars(PRecover(p))
       /\ SF_vars(\E v \in Votes : PVote(p, v))
       /\ SF_vars(\E v \in Votes : CoordReceiveVote(p, v))
       /\ SF_vars(\E d \in Decisions : PReceiveDecision(p, d))

Spec == Init /\ [][Next]_vars /\ Fairness

(************************** Safety invariants *****************************)

\* Agreement: no two participants decide differently. The check covers
\* all participants, including those that crashed.
Agreement ==
  \A p, q \in participants :
    (pDecision[p] # undecided /\ pDecision[q] # undecided)
       => pDecision[p] = pDecision[q]

\* Participant decisions are consistent with the coordinator's decision.
CoordConsistency ==
  \A p \in participants :
    pDecision[p] \in Decisions /\ coordState \in Decisions
       => pDecision[p] = coordState

\* Validity: commit is possible only if every participant voted yes.
CommitValidity ==
  /\ (coordState = commit) => \A p \in participants : voteSent[p] = yes
  /\ \A p \in participants :
       pDecision[p] = commit => \A q \in participants : voteSent[q] = yes

\* Validity: any no vote forces the outcome to be abort.
AbortValidity ==
  (\E p \in participants : voteSent[p] = no)
     => /\ coordState # commit
        /\ \A q \in participants : pDecision[q] # commit

Inv == TypeOK /\ Agreement /\ CoordConsistency /\ CommitValidity /\ AbortValidity

(************************* Temporal properties ****************************)

\* Integrity: once a participant decides, it never reverts.
Integrity ==
  [][\A p \in participants :
        pDecision[p] # undecided => pDecision'[p] = pDecision[p]]_vars

CoordIntegrity ==
  [][coordState # waiting => coordState' = coordState]_vars

\* Weak liveness: if the coordinator is eventually up forever and every
\* participant is eventually up forever, all participants eventually decide.
Termination ==
  ((<>[]coordAlive) /\ (\A p \in participants : <>[]pAlive[p]))
     => <>(\A p \in participants : pDecision[p] # undecided)

\* Under the bounded failure model above, the same conclusion holds
\* without the hypothesis.
EventualDecision ==
  <>(\A p \in participants : pDecision[p] # undecided)

\* Non-triviality: commit stays reachable. TLC should find a violation
\* of this property, which serves as a witness that commit can happen.
NeverCommit == coordState # commit

(*************************** Symmetry reduction ***************************)
\* Participants are interchangeable. Use only for safety checking, since
\* TLC symmetry reduction is unsound for some liveness properties.
Symmetry == Permutations(participants)

=============================================================================