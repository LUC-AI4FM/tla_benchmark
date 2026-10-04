---------------------------- MODULE nbac ----------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

Procs == 1..N

VARIABLES
    vote,
    crashed,
    suspected,
    decision,
    sent,
    received

vars == <<vote, crashed, suspected, decision, sent, received>>

Message == [type : {"VOTE", "DECISION"}, src : Procs, val : {"YES", "NO", "ABORT", "COMMIT"}]

TypeOK ==
    /\ vote \in [Procs -> {"YES", "NO", "NONE"}]
    /\ crashed \in SUBSET Procs
    /\ suspected \in SUBSET Procs
    /\ decision \in [Procs -> {"ABORT", "COMMIT", "NONE"}]
    /\ sent \subseteq Message
    /\ received \in [Procs -> SUBSET Message]

InitAllYes ==
    /\ vote = [p \in Procs |-> "YES"]
    /\ crashed = {}
    /\ suspected = {}
    /\ decision = [p \in Procs |-> "NONE"]
    /\ sent = {}
    /\ received = [p \in Procs |-> {}]

InitAllNo ==
    /\ vote = [p \in Procs |-> "NO"]
    /\ crashed = {}
    /\ suspected = {}
    /\ decision = [p \in Procs |-> "NONE"]
    /\ sent = {}
    /\ received = [p \in Procs |-> {}]

Init == InitAllYes \/ InitAllNo

SendVote(p) ==
    /\ p \notin crashed
    /\ vote[p] /= "NONE"
    /\ LET msg == [type |-> "VOTE", src |-> p, val |-> vote[p]]
       IN /\ msg \notin sent
          /\ sent' = sent \cup {msg}
    /\ UNCHANGED <<vote, crashed, suspected, decision, received>>

ReceiveMessage(p) ==
    /\ p \notin crashed
    /\ \E msg \in sent :
        /\ msg \notin received[p]
        /\ received' = [received EXCEPT ![p] = @ \cup {msg}]
    /\ UNCHANGED <<vote, crashed, suspected, decision, sent>>

Crash(p) ==
    /\ p \notin crashed
    /\ crashed' = crashed \cup {p}
    /\ UNCHANGED <<vote, suspected, decision, sent, received>>

Suspect(p) ==
    /\ p \notin suspected
    /\ suspected' = suspected \cup {p}
    /\ UNCHANGED <<vote, crashed, decision, sent, received>>

ReceivedVotes(p) ==
    {msg \in received[p] : msg.type = "VOTE"}

AllVotesReceived(p) ==
    \A q \in Procs : \E msg \in ReceivedVotes(p) : msg.src = q

AllVotesYes(p) ==
    \A msg \in ReceivedVotes(p) : msg.val = "YES"

SomeVoteNo(p) ==
    \E msg \in ReceivedVotes(p) : msg.val = "NO"

SomeSuspected ==
    suspected /= {}

ReceivedDecision(p, d) ==
    \E msg \in received[p] : msg.type = "DECISION" /\ msg.val = d

DecideCommit(p) ==
    /\ p \notin crashed
    /\ decision[p] = "NONE"
    /\ AllVotesReceived(p)
    /\ AllVotesYes(p)
    /\ ~SomeSuspected
    /\ decision' = [decision EXCEPT ![p] = "COMMIT"]
    /\ LET msg == [type |-> "DECISION", src |-> p, val |-> "COMMIT"]
       IN sent' = sent \cup {msg}
    /\ UNCHANGED <<vote, crashed, suspected, received>>

DecideAbort(p) ==
    /\ p \notin crashed
    /\ decision[p] = "NONE"
    /\ \/ SomeVoteNo(p)
       \/ SomeSuspected
       \/ ReceivedDecision(p, "ABORT")
    /\ decision' = [decision EXCEPT ![p] = "ABORT"]
    /\ LET msg == [type |-> "DECISION", src |-> p, val |-> "ABORT"]
       IN sent' = sent \cup {msg}
    /\ UNCHANGED <<vote, crashed, suspected, received>>

DecideFromMessage(p) ==
    /\ p \notin crashed
    /\ decision[p] = "NONE"
    /\ \/ /\ ReceivedDecision(p, "COMMIT")
          /\ decision' = [decision EXCEPT ![p] = "COMMIT"]
          /\ LET msg == [type |-> "DECISION", src |-> p, val |-> "COMMIT"]
             IN sent' = sent \cup {msg}
       \/ /\ ReceivedDecision(p, "ABORT")
          /\ decision' = [decision EXCEPT ![p] = "ABORT"]
          /\ LET msg == [type |-> "DECISION", src |-> p, val |-> "ABORT"]
             IN sent' = sent \cup {msg}
    /\ UNCHANGED <<vote, crashed, suspected, received>>

ProcessAction(p) ==
    \/ SendVote(p)
    \/ ReceiveMessage(p)
    \/ DecideCommit(p)
    \/ DecideAbort(p)
    \/ DecideFromMessage(p)

EnvironmentAction ==
    \E p \in Procs :
        \/ Crash(p)
        \/ Suspect(p)

Next ==
    \/ \E p \in Procs : ProcessAction(p)
    \/ EnvironmentAction

Fairness ==
    /\ \A p \in Procs : WF_vars(SendVote(p))
    /\ \A p \in Procs : WF_vars(ReceiveMessage(p))
    /\ \A p \in Procs : WF_vars(DecideCommit(p))
    /\ \A p \in Procs : WF_vars(DecideAbort(p))
    /\ \A p \in Procs : WF_vars(DecideFromMessage(p))

Spec == Init /\ [][Next]_vars /\ Fairness

Agreement ==
    \A p, q \in Procs :
        (decision[p] /= "NONE" /\ decision[q] /= "NONE") =>
            decision[p] = decision[q]

AgrrLtl == []Agreement

AbortValidity ==
    \A p \in Procs :
        decision[p] = "ABORT" =>
            (\E q \in Procs : vote[q] = "NO") \/ (suspected /= {})

AbortValidityLtl == []AbortValidity

CommitValidity ==
    \A p \in Procs :
        decision[p] = "COMMIT" =>
            \A q \in Procs : vote[q] = "YES"

CommitValidityLtl == []CommitValidity

Termination ==
    \A p \in Procs :
        (p \notin crashed) => <>(decision[p] /= "NONE")

TerminationLtl == Termination

EventualCommit ==
    (\A p \in Procs : vote[p] = "YES") /\ (crashed = {}) /\ (suspected = {}) =>
        <>(\E p \in Procs : decision[p] = "COMMIT")

EventualCommitLtl == EventualCommit

=========================================================================