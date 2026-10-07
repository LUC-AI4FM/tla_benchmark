----------------------------- MODULE AtomicCommitFD -----------------------------

EXTENDS TLC

CONSTANTS Proc, Mode

ASSUME Mode \in {"AllYes", "AllNo"}

(*
  Values, message types, and message structure
*)
Val == {"YES", "NO"}
Dec == {"commit", "abort"}
StatusVals == {"undecided"} \cup Dec
MType == {"VOTE", "DECIDE"}
Msg == [type: MType, from: Proc, to: Proc, val: Val \cup Dec]

VARIABLES
  votes,        \* [Proc -> Val]
  status,       \* [Proc -> StatusVals]
  crashed,      \* SUBSET Proc
  Suspected,    \* SUBSET Proc (output of failure detector)
  sentVote,     \* [Proc -> BOOLEAN]
  sentDecide,   \* [Proc -> BOOLEAN]
  msgs,         \* SUBSET Msg
  inbox         \* [Proc -> SUBSET Msg]

vars == << votes, status, crashed, Suspected, sentVote, sentDecide, msgs, inbox >>

(*
  Initial condition: specialized to all-YES or all-NO votes
*)
Init ==
  /\ votes = [p \in Proc |-> IF Mode = "AllYes" THEN "YES" ELSE "NO"]
  /\ status = [p \in Proc |-> "undecided"]
  /\ crashed = {}
  /\ Suspected = {}
  /\ sentVote = [p \in Proc |-> FALSE]
  /\ sentDecide = [p \in Proc |-> FALSE]
  /\ msgs = {}
  /\ inbox = [p \in Proc |-> {}]

(*
  Helper predicates and message sets
*)
VoteMsgs(p) == { [type |-> "VOTE", from |-> p, to |-> q, val |-> votes[p]] : q \in Proc }
DecideMsgs(p) == { [type |-> "DECIDE", from |-> p, to |-> q, val |-> status[p]] : q \in Proc }

ReceivedYesFrom(p, r) ==
  \E m \in inbox[p] : m.type = "VOTE" /\ m.from = r /\ m.val = "YES"

ReceivedNo(p) ==
  \E m \in inbox[p] : m.type = "VOTE" /\ m.val = "NO"

(*
  Process-local actions
*)
SendVote(p) ==
  /\ p \in Proc
  /\ ~sentVote[p]
  /\ p \notin crashed
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ msgs' = msgs \cup VoteMsgs(p)
  /\ UNCHANGED << votes, status, crashed, Suspected, sentDecide, inbox >>

LocalAbort(p) ==
  /\ p \in Proc
  /\ p \notin crashed
  /\ status[p] = "undecided"
  /\ ( ReceivedNo(p) \/ ((Suspected \ {p}) # {}) )
  /\ status' = [status EXCEPT ![p] = "abort"]
  /\ UNCHANGED << votes, crashed, Suspected, sentVote, sentDecide, msgs, inbox >>

LocalCommit(p) ==
  /\ p \in Proc
  /\ p \notin crashed
  /\ status[p] = "undecided"
  /\ Suspected = {}
  /\ \A r \in Proc : ReceivedYesFrom(p, r)
  /\ status' = [status EXCEPT ![p] = "commit"]
  /\ UNCHANGED << votes, crashed, Suspected, sentVote, sentDecide, msgs, inbox >>

BroadcastDecision(p) ==
  /\ p \in Proc
  /\ p \notin crashed
  /\ status[p] \in Dec
  /\ ~sentDecide[p]
  /\ sentDecide' = [sentDecide EXCEPT ![p] = TRUE]
  /\ msgs' = msgs \cup DecideMsgs(p)
  /\ UNCHANGED << votes, status, crashed, Suspected, sentVote, inbox >>

RecvDecide(p) ==
  /\ p \in Proc
  /\ p \notin crashed
  /\ status[p] = "undecided"
  /\ \E m \in inbox[p] : m.type = "DECIDE"
  /\ LET md == CHOOSE m \in inbox[p] : m.type = "DECIDE"
     IN /\ status' = [status EXCEPT ![p] =
                          IF md.val = "commit" THEN "commit" ELSE "abort"]
        /\ inbox' = [inbox EXCEPT ![p] = @ \ {md}]
        /\ UNCHANGED << votes, crashed, Suspected, sentVote, sentDecide, msgs >>

(*
  Environment actions: message delivery, crashes, and failure-detector updates
*)
Deliver ==
  /\ msgs # {}
  /\ LET md == CHOOSE m \in msgs : TRUE
     IN /\ msgs' = msgs \ {md}
        /\ inbox' = [inbox EXCEPT ![md.to] = @ \cup {md}]
        /\ UNCHANGED << votes, status, crashed, Suspected, sentVote, sentDecide >>

Crash(p) ==
  /\ p \in Proc
  /\ p \notin crashed
  /\ crashed' = crashed \cup {p}
  /\ UNCHANGED << votes, status, Suspected, sentVote, sentDecide, msgs, inbox >>

SuspectStep ==
  /\ Suspected' \subseteq Proc
  /\ UNCHANGED << votes, status, crashed, sentVote, sentDecide, msgs, inbox >>

(*
  Aggregated per-process action for fairness
*)
PAction(p) ==
  SendVote(p) \/ LocalAbort(p) \/ LocalCommit(p) \/ BroadcastDecision(p) \/ RecvDecide(p)

(*
  Next-state relation
*)
Next ==
  \E p \in Proc : (Crash(p) \/ PAction(p))
  \/ Deliver
  \/ SuspectStep

(*
  Specification with weak fairness for non-stuttering process actions
*)
Spec ==
  Init /\ [][Next]_vars /\ \A p \in Proc : WF_vars(PAction(p))

(*
  Type invariant
*)
TypeInv ==
  /\ votes \in [Proc -> Val]
  /\ status \in [Proc -> StatusVals]
  /\ crashed \subseteq Proc
  /\ Suspected \subseteq Proc
  /\ sentVote \in [Proc -> BOOLEAN]
  /\ sentDecide \in [Proc -> BOOLEAN]
  /\ msgs \subseteq Msg
  /\ inbox \in [Proc -> SUBSET Msg]

(*
  Safety properties
*)
AgreementState ==
  \A p \in Proc : \A q \in Proc :
    (status[p] \in Dec /\ status[q] \in Dec) => status[p] = status[q]

Agreement == []AgreementState

AbortValidity ==
  IF Mode = "AllNo" THEN [](\A p \in Proc : status[p] # "commit") ELSE TRUE

CommitValidity ==
  IF Mode = "AllYes" THEN ([](crashed = {})) => [](\A p \in Proc : status[p] # "abort") ELSE TRUE

(*
  Liveness properties
*)
AllDecided == \A p \in Proc : status[p] \in Dec

FDEventualAccuracy ==
  \A p \in Proc : [](p \notin crashed => <>(p \notin Suspected))

EventuallyStableCrashes ==
  <><> (TRUE) /\ <>[](\E C \in SUBSET Proc : crashed = C)

(*
  Termination: every non-crashed process eventually decides (unless it later crashes)
*)
Termination ==
  \A p \in Proc : [](p \notin crashed => <>( (status[p] \in Dec) \/ (p \in crashed) ))

(*
  Eventual commit: under all-YES votes, eventual crash quiescence, and eventual FD accuracy,
  eventually all processes commit.
*)
EventualCommit ==
  (Mode = "AllYes") /\ EventuallyStableCrashes /\ FDEventualAccuracy
    => <>(\A p \in Proc : status[p] = "commit")

=============================================================================