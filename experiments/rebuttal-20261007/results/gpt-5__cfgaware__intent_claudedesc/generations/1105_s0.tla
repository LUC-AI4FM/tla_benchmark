------------------------------ MODULE NBAC ------------------------------

EXTENDS Naturals

CONSTANT N

Proc == 1..N
VOTE == {"YES", "NO"}
DECISION == {"UNDECIDED", "COMMIT", "ABORT"}

VARIABLES votes, sent, rcvd, decision, crashed, suspected

vars == << votes, sent, rcvd, decision, crashed, suspected >>

TypeOK ==
  /\ votes \in [Proc -> VOTE]
  /\ sent \in [Proc -> BOOLEAN]
  /\ rcvd \in [Proc -> SUBSET Proc]
  /\ decision \in [Proc -> DECISION]
  /\ crashed \subseteq Proc
  /\ suspected \subseteq Proc

BaseInit ==
  /\ sent = [p \in Proc |-> FALSE]
  /\ rcvd = [p \in Proc |-> {}]
  /\ decision = [p \in Proc |-> "UNDECIDED"]
  /\ crashed = {}
  /\ suspected \in SUBSET Proc

InitArb ==
  /\ BaseInit
  /\ votes \in [Proc -> VOTE]

InitAllYes ==
  /\ BaseInit
  /\ votes = [p \in Proc |-> "YES"]

InitAllNo ==
  /\ BaseInit
  /\ votes = [p \in Proc |-> "NO"]

Init == InitArb \/ InitAllYes \/ InitAllNo

SendVote(p) ==
  /\ p \in Proc
  /\ ~(p \in crashed)
  /\ ~sent[p]
  /\ sent' = [sent EXCEPT ![p] = TRUE]
  /\ UNCHANGED << votes, rcvd, decision, crashed, suspected >>

Recv(p, q) ==
  /\ p \in Proc /\ q \in Proc
  /\ ~(p \in crashed)
  /\ sent[p]                         \* a process receives only after it has sent its own vote
  /\ sent[q]
  /\ ~(q \in rcvd[p])
  /\ rcvd' = [rcvd EXCEPT ![p] = @ \cup {q}]
  /\ UNCHANGED << votes, sent, decision, crashed, suspected >>

HasNo(p) == \E q \in rcvd[p] : votes[q] = "NO"

DecideAbort(p) ==
  /\ p \in Proc
  /\ ~(p \in crashed)
  /\ decision[p] = "UNDECIDED"
  /\ (HasNo(p) \/ (suspected # {}))
  /\ decision' = [decision EXCEPT ![p] = "ABORT"]
  /\ UNCHANGED << votes, sent, rcvd, crashed, suspected >>

DecideCommit(p) ==
  /\ p \in Proc
  /\ ~(p \in crashed)
  /\ decision[p] = "UNDECIDED"
  /\ rcvd[p] = Proc
  /\ (\A q \in Proc : votes[q] = "YES")
  /\ suspected = {}
  /\ decision' = [decision EXCEPT ![p] = "COMMIT"]
  /\ UNCHANGED << votes, sent, rcvd, crashed, suspected >>

Crash(p) ==
  /\ p \in Proc
  /\ ~(p \in crashed)
  /\ crashed' = crashed \cup {p}
  /\ UNCHANGED << votes, sent, rcvd, decision, suspected >>

SuspectStep ==
  /\ \E S \in SUBSET Proc : suspected' = S
  /\ UNCHANGED << votes, sent, rcvd, decision, crashed >>

Receive(p) == \E q \in Proc : Recv(p, q)

NonCrash(p) == SendVote(p) \/ Receive(p) \/ DecideAbort(p) \/ DecideCommit(p)

Next ==
  \/ (\E p \in Proc :
        SendVote(p)
      \/ Receive(p)
      \/ DecideAbort(p)
      \/ DecideCommit(p)
      \/ Crash(p))
  \/ SuspectStep

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Proc : WF_vars(NonCrash(p))

DifferentDecisions ==
  \E p \in Proc, q \in Proc :
    /\ p # q
    /\ decision[p] = "COMMIT"
    /\ decision[q] = "ABORT"

AgrrLtl == [] ~DifferentDecisions

AbortValidityLtl ==
  (\E p \in Proc : votes[p] = "NO")
    => [] (\A q \in Proc : decision[q] # "COMMIT")

CommitValidityLtl ==
  ((\A p \in Proc : votes[p] = "YES") /\ [] (suspected = {}))
    => [] (\A q \in Proc : decision[q] # "ABORT")

TerminationLtl ==
  (([] (crashed = {})) /\ ([] (suspected = {})))
    => (\A p \in Proc : <> (decision[p] # "UNDECIDED"))

=============================================================================