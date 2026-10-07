----------------------------- MODULE AC_NonBlocking_FD -----------------------------

EXTENDS Naturals

CONSTANTS Proc

ASSUME Proc /= {}

(*
  Values and message types
*)
Vote == {"Yes", "No"}
DecisionVal == {"Commit", "Abort"}
MaybeVote == Vote \cup {"None"}
MsgType == {"VOTE", "DECIDE"}
Message == [type: MsgType, from: Proc, to: Proc, val: Vote \cup DecisionVal]

VARIABLES
  vote,         \* [Proc -> Vote]
  crashed,      \* SUBSET Proc
  suspect,      \* [Proc -> SUBSET Proc]
  msgs,         \* SUBSET Message
  recvdVote,    \* [Proc -> [Proc -> MaybeVote]]
  decision,     \* [Proc -> ({"Undecided"} \cup DecisionVal)]
  sentVoteTo,   \* [Proc -> SUBSET Proc], tracks vote broadcasts
  sentDecTo     \* [Proc -> SUBSET Proc], tracks decision broadcasts

vars == << vote, crashed, suspect, msgs, recvdVote, decision, sentVoteTo, sentDecTo >>

(*
  Helper predicates
*)
CanCommit(p) == \A q \in Proc: recvdVote[p][q] = "Yes"
KnowsNo(p) == vote[p] = "No" \/ (\E q \in Proc: recvdVote[p][q] = "No")

(*
  Initial conditions: generic and specialized
*)
GenInit ==
  /\ vote \in [Proc -> Vote]
  /\ crashed = {}
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ \A p \in Proc: suspect[p] = {}
  /\ msgs = {}
  /\ recvdVote \in [Proc -> [Proc -> MaybeVote]]
  /\ \A p \in Proc:
       recvdVote[p] = [q \in Proc |-> IF q = p THEN vote[p] ELSE "None"]
  /\ decision = [p \in Proc |-> "Undecided"]
  /\ sentVoteTo = [p \in Proc |-> {}]
  /\ sentDecTo  = [p \in Proc |-> {}]

AllYesInit ==
  /\ GenInit
  /\ \A p \in Proc: vote[p] = "Yes"

AllNoInit ==
  /\ GenInit
  /\ \A p \in Proc: vote[p] = "No"

Init == GenInit

(*
  Process-local actions
*)
SendVotes(p) ==
  /\ p \in Proc
  /\ p \notin crashed
  /\ sentVoteTo[p] /= Proc
  /\ LET dst == Proc \ sentVoteTo[p] IN
       /\ msgs' = msgs \cup { [type |-> "VOTE", from |-> p, to |-> q, val |-> vote[p]] : q \in dst }
       /\ sentVoteTo' = [sentVoteTo EXCEPT ![p] = Proc]
       /\ UNCHANGED << vote, crashed, suspect, recvdVote, decision, sentDecTo >>

ReceiveVoteStep(p) ==
  /\ p \in Proc
  /\ p \notin crashed
  /\ \E m \in msgs: m.type = "VOTE" /\ m.to = p
  /\ LET m == CHOOSE r \in msgs: r.type = "VOTE" /\ r.to = p IN
     LET q == m.from IN
       /\ msgs' = msgs \ { m }
       /\ recvdVote' = [recvdVote EXCEPT ![p][q] = m.val]
       /\ UNCHANGED << vote, crashed, suspect, decision, sentVoteTo, sentDecTo >>

DecideAbort(p) ==
  /\ p \in Proc
  /\ p \notin crashed
  /\ decision[p] = "Undecided"
  /\ KnowsNo(p)
  /\ decision' = [decision EXCEPT ![p] = "Abort"]
  /\ UNCHANGED << vote, crashed, suspect, msgs, recvdVote, sentVoteTo, sentDecTo >>

DecideCommit(p) ==
  /\ p \in Proc
  /\ p \notin crashed
  /\ decision[p] = "Undecided"
  /\ CanCommit(p)
  /\ decision' = [decision EXCEPT ![p] = "Commit"]
  /\ UNCHANGED << vote, crashed, suspect, msgs, recvdVote, sentVoteTo, sentDecTo >>

BroadcastDecision(p) ==
  /\ p \in Proc
  /\ p \notin crashed
  /\ decision[p] \in DecisionVal
  /\ sentDecTo[p] /= Proc
  /\ LET dst == Proc \ sentDecTo[p] IN
       /\ msgs' = msgs \cup { [type |-> "DECIDE", from |-> p, to |-> q, val |-> decision[p]] : q \in dst }
       /\ sentDecTo' = [sentDecTo EXCEPT ![p] = Proc]
       /\ UNCHANGED << vote, crashed, suspect, recvdVote, decision, sentVoteTo >>

ReceiveDecideStep(p) ==
  /\ p \in Proc
  /\ p \notin crashed
  /\ decision[p] = "Undecided"
  /\ \E m \in msgs: m.type = "DECIDE" /\ m.to = p
  /\ LET m == CHOOSE r \in msgs: r.type = "DECIDE" /\ r.to = p IN
       /\ msgs' = msgs \ { m }
       /\ decision' = [decision EXCEPT ![p] = m.val]
       /\ UNCHANGED << vote, crashed, suspect, recvdVote, sentVoteTo, sentDecTo >>

SuspectStep(p) ==
  /\ p \in Proc
  /\ p \notin crashed
  /\ suspect[p] /= Proc
  /\ LET q == CHOOSE r \in (Proc \ suspect[p]): TRUE IN
       /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup { q }]
       /\ UNCHANGED << vote, crashed, msgs, recvdVote, decision, sentVoteTo, sentDecTo >>

(*
  Environment action
*)
Crash(q) ==
  /\ q \in Proc
  /\ q \notin crashed
  /\ crashed' = crashed \cup { q }
  /\ UNCHANGED << vote, suspect, msgs, recvdVote, decision, sentVoteTo, sentDecTo >>

ProcessStep(p) ==
  SendVotes(p)
  \/ ReceiveVoteStep(p)
  \/ DecideAbort(p)
  \/ DecideCommit(p)
  \/ BroadcastDecision(p)
  \/ ReceiveDecideStep(p)
  \/ SuspectStep(p)

Next ==
  (\E p \in Proc: ProcessStep(p))
  \/ (\E q \in Proc: Crash(q))

(*
  Type invariant
*)
TypeInv ==
  /\ vote \in [Proc -> Vote]
  /\ crashed \subseteq Proc
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ msgs \subseteq Message
  /\ recvdVote \in [Proc -> [Proc -> MaybeVote]]
  /\ decision \in [Proc -> ({"Undecided"} \cup DecisionVal)]
  /\ sentVoteTo \in [Proc -> SUBSET Proc]
  /\ sentDecTo \in [Proc -> SUBSET Proc]

(*
  Safety properties
*)
Agreement ==
  [] (\A p \in Proc: \A q \in Proc:
        (decision[p] \in DecisionVal /\ decision[q] \in DecisionVal) => decision[p] = decision[q])

AbortValidity ==
  [] ((\E q \in Proc: vote[q] = "No") => ~(\E p \in Proc: decision[p] = "Commit"))

CommitValidity ==
  [] (\A p \in Proc: (decision[p] = "Commit") => (\A q \in Proc: vote[q] = "Yes"))

(*
  Liveness properties
*)
Termination ==
  \A p \in Proc: ([](p \notin crashed)) => (<>(decision[p] /= "Undecided"))

EventualCommit ==
  (((\A p \in Proc: vote[p] = "Yes") /\ [](crashed = {}))
    => (<>(\A p \in Proc: decision[p] = "Commit")))

Spec ==
  Init /\ [][Next]_vars /\ (\A p \in Proc: WF_vars(ProcessStep(p)))

==================================================================================