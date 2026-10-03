---------------------------- MODULE nbac_failure_detector ----------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

ASSUME N \in Nat /\ N > 0

Procs == 1..N

Votes == {"YES", "NO"}
Decisions == {"COMMIT", "ABORT"}
States == {"WORKING", "READY", "DECIDED"}

VARIABLE vote
VARIABLE state
VARIABLE decision
VARIABLE crashed
VARIABLE suspected
VARIABLE msgs
VARIABLE received

vars == <<vote, state, decision, crashed, suspected, msgs, received>>

TypeOK ==
    /\ vote \in [Procs -> Votes]
    /\ state \in [Procs -> States]
    /\ decision \in [Procs -> Decisions \cup {"NONE"}]
    /\ crashed \in SUBSET Procs
    /\ suspected \in SUBSET Procs
    /\ msgs \in SUBSET (Procs \X Procs \X (Votes \cup Decisions \cup {"READY"}))
    /\ received \in [Procs -> SUBSET (Procs \X (Votes \cup Decisions \cup {"READY"}))]

AllYes ==
    /\ vote = [p \in Procs |-> "YES"]
    /\ state = [p \in Procs |-> "WORKING"]
    /\ decision = [p \in Procs |-> "NONE"]
    /\ crashed = {}
    /\ suspected = {}
    /\ msgs = {}
    /\ received = [p \in Procs |-> {}]

AllNo ==
    /\ vote = [p \in Procs |-> "NO"]
    /\ state = [p \in Procs |-> "WORKING"]
    /\ decision = [p \in Procs |-> "NONE"]
    /\ crashed = {}
    /\ suspected = {}
    /\ msgs = {}
    /\ received = [p \in Procs |-> {}]

Init == AllYes \/ AllNo

Broadcast(p, m) ==
    msgs' = msgs \cup {<<p, q, m>> : q \in Procs}

SendVote(p) ==
    /\ p \notin crashed
    /\ state[p] = "WORKING"
    /\ Broadcast(p, vote[p])
    /\ state' = [state EXCEPT ![p] = "READY"]
    /\ UNCHANGED <<vote, decision, crashed, suspected, received>>

Receive(p) ==
    /\ p \notin crashed
    /\ \E sender \in Procs, m \in (Votes \cup Decisions \cup {"READY"}) :
        /\ <<sender, p, m>> \in msgs
        /\ <<sender, m>> \notin received[p]
        /\ received' = [received EXCEPT ![p] = @ \cup {<<sender, m>>}]
        /\ UNCHANGED <<vote, state, decision, crashed, suspected, msgs>>

ReceivedVotesFrom(p) == {q \in Procs : \E v \in Votes : <<q, v>> \in received[p]}

AllVotesReceived(p) == ReceivedVotesFrom(p) = Procs

AllVotedYes(p) == \A q \in Procs : <<q, "YES">> \in received[p]

SomeVotedNo(p) == \E q \in Procs : <<q, "NO">> \in received[p]

SomeSuspected(p) == suspected /= {}

DecideCommit(p) ==
    /\ p \notin crashed
    /\ state[p] \in {"WORKING", "READY"}
    /\ decision[p] = "NONE"
    /\ AllVotesReceived(p)
    /\ AllVotedYes(p)
    /\ ~SomeSuspected(p)
    /\ decision' = [decision EXCEPT ![p] = "COMMIT"]
    /\ state' = [state EXCEPT ![p] = "DECIDED"]
    /\ Broadcast(p, "COMMIT")
    /\ UNCHANGED <<vote, crashed, suspected, received>>

DecideAbort(p) ==
    /\ p \notin crashed
    /\ state[p] \in {"WORKING", "READY"}
    /\ decision[p] = "NONE"
    /\ \/ SomeVotedNo(p)
       \/ SomeSuspected(p)
    /\ decision' = [decision EXCEPT ![p] = "ABORT"]
    /\ state' = [state EXCEPT ![p] = "DECIDED"]
    /\ Broadcast(p, "ABORT")
    /\ UNCHANGED <<vote, crashed, suspected, received>>

ReceiveDecision(p) ==
    /\ p \notin crashed
    /\ decision[p] = "NONE"
    /\ \E q \in Procs, d \in Decisions :
        /\ <<q, d>> \in received[p]
        /\ decision' = [decision EXCEPT ![p] = d]
        /\ state' = [state EXCEPT ![p] = "DECIDED"]
        /\ Broadcast(p, d)
        /\ UNCHANGED <<vote, crashed, suspected, received>>

Crash(p) ==
    /\ p \notin crashed
    /\ crashed' = crashed \cup {p}
    /\ UNCHANGED <<vote, state, decision, suspected, msgs, received>>

Suspect(p) ==
    /\ p \notin suspected
    /\ suspected' = suspected \cup {p}
    /\ UNCHANGED <<vote, state, decision, crashed, msgs, received>>

ProcessAction(p) ==
    \/ SendVote(p)
    \/ Receive(p)
    \/ DecideCommit(p)
    \/ DecideAbort(p)
    \/ ReceiveDecision(p)

EnvironmentAction ==
    \E p \in Procs :
        \/ Crash(p)
        \/ Suspect(p)

Next ==
    \/ \E p \in Procs : ProcessAction(p)
    \/ EnvironmentAction

Fairness ==
    /\ \A p \in Procs : WF_vars(SendVote(p))
    /\ \A p \in Procs : WF_vars(Receive(p))
    /\ \A p \in Procs : WF_vars(DecideCommit(p))
    /\ \A p \in Procs : WF_vars(DecideAbort(p))
    /\ \A p \in Procs : WF_vars(ReceiveDecision(p))

Spec == Init /\ [][Next]_vars /\ Fairness

Agreement ==
    \A p, q \in Procs :
        (decision[p] \in Decisions /\ decision[q] \in Decisions) => (decision[p] = decision[q])

AgrrLtl == []Agreement

AbortValidity ==
    \A p \in Procs :
        (decision[p] = "ABORT") =>
            (\E q \in Procs : vote[q] = "NO") \/ (crashed /= {})

AbortValidityLtl == []AbortValidity

CommitValidity ==
    \A p \in Procs :
        (decision[p] = "COMMIT") =>
            (\A q \in Procs : vote[q] = "YES")

CommitValidityLtl == []CommitValidity

Termination ==
    (\A p \in Procs : p \notin crashed) =>
        (\A p \in Procs : decision[p] \in Decisions)

TerminationLtl == <>Termination

EventualCommit ==
    (\A p \in Procs : vote[p] = "YES") /\ (crashed = {}) =>
        <>(\E p \in Procs : decision[p] = "COMMIT")

EventualCommitLtl == EventualCommit

=============================================================================