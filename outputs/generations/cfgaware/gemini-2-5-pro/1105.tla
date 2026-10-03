-------------------------- MODULE NBAC --------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS N, vote

ASSUME N \in Nat /\ N > 0
ASSUME vote \in [1..N -> {"YES", "NO"}]
ASSUME (\A p \in 1..N: vote[p] = "YES") \/ (\A p \in 1..N: vote[p] = "NO")

Process == 1..N
DecisionValue == {"commit", "abort", "undecided"}
MessageContent == {"YES", "ABORT"}
Message == [type: MessageContent, from: Process]

VARIABLES pc, decision, waitfor, crashed, suspected, messages

vars == <<pc, decision, waitfor, crashed, suspected, messages>>

TypeOK ==
    /\ pc \in [Process -> {"init", "waiting", "done"}]
    /\ decision \in [Process -> DecisionValue]
    /\ waitfor \in [Process -> SUBSET Process]
    /\ crashed \in SUBSET Process
    /\ suspected \in [Process -> SUBSET Process]
    /\ messages \in SUBSET Message

Init ==
    /\ pc = [p \in Process |-> "init"]
    /\ decision = [p \in Process |-> "undecided"]
    /\ waitfor = [p \in Process |-> Process]
    /\ crashed = {}
    /\ suspected = [p \in Process |-> {}]
    /\ messages = {}

Vote(p) ==
    /\ p \notin crashed
    /\ pc[p] = "init"
    /\ IF vote[p] = "NO"
       THEN /\ decision' = [decision EXCEPT ![p] = "abort"]
            /\ pc' = [pc EXCEPT ![p] = "done"]
            /\ messages' = messages \cup {[type |-> "ABORT", from |-> p]}
            /\ UNCHANGED <<waitfor, crashed, suspected>>
       ELSE /\ pc' = [pc EXCEPT ![p] = "waiting"]
            /\ messages' = messages \cup {[type |-> "YES", from |-> p]}
            /\ UNCHANGED <<decision, waitfor, crashed, suspected>>

Receive(p, msg) ==
    /\ p \notin crashed
    /\ pc[p] = "waiting"
    /\ msg \in messages
    /\ IF msg.type = "ABORT"
       THEN /\ decision' = [decision EXCEPT ![p] = "abort"]
            /\ pc' = [pc EXCEPT ![p] = "done"]
            /\ messages' = messages \cup {[type |-> "ABORT", from |-> p]}
            /\ UNCHANGED <<waitfor, crashed, suspected>>
       ELSE /\ waitfor' = [waitfor EXCEPT ![p] = @ \ {msg.from}]
            /\ UNCHANGED <<pc, decision, messages, crashed, suspected>>

DecideCommit(p) ==
    /\ p \notin crashed
    /\ pc[p] = "waiting"
    /\ waitfor[p] = {}
    /\ decision' = [decision EXCEPT ![p] = "commit"]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<waitfor, messages, crashed, suspected>>

DecideAbortOnSuspicion(p) ==
    /\ p \notin crashed
    /\ pc[p] = "waiting"
    /\ waitfor[p] # {}
    /\ waitfor[p] \subseteq suspected[p]
    /\ decision' = [decision EXCEPT ![p] = "abort"]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ messages' = messages \cup {[type |-> "ABORT", from |-> p]}
    /\ UNCHANGED <<waitfor, crashed, suspected>>

Crash(p) ==
    /\ p \notin crashed
    /\ crashed' = crashed \cup {p}
    /\ UNCHANGED <<pc, decision, waitfor, messages, suspected>>

Suspect(p, q) ==
    /\ p \notin crashed
    /\ q \notin suspected[p]
    /\ suspected' = [suspected EXCEPT ![p] = @ \cup {q}]
    /\ UNCHANGED <<pc, decision, waitfor, messages, crashed>>

Unsuspect(p, q) ==
    /\ p \notin crashed
    /\ q \in suspected[p]
    /\ suspected' = [suspected EXCEPT ![p] = @ \ {q}]
    /\ UNCHANGED <<pc, decision, waitfor, messages, crashed>>

ProcessAction(p) ==
    \/ Vote(p)
    \/ DecideCommit(p)
    \/ DecideAbortOnSuspicion(p)
    \/ \E msg \in messages: Receive(p, msg)

Next ==
    \/ \E p \in Process: ProcessAction(p)
    \/ \E p \in Process: Crash(p)
    \/ \E p, q \in Process: Suspect(p, q) \/ Unsuspect(p, q)
    \/ UNCHANGED vars

Fairness == \A p \in Process: WF_vars(ProcessAction(p))

Spec == Init /\ [][Next]_vars

\* Temporal Properties

AgrrLtl ==
    [](\A p, q \in Process:
        (decision[p] # "undecided" /\ decision[q] # "undecided")
            => (decision[p] = decision[q]))

CommitValidityLtl ==
    [](\A p \in Process:
        (decision[p] = "commit") => (\A q \in Process: vote[q] = "YES"))

AbortValidityLtl ==
    ((\A p \in Process: vote[p] = "YES") /\ [](crashed = {}))
        => [](\A p \in Process: decision[p] # "abort")

TerminationLtl ==
    \A p \in Process:
        ([](p \notin crashed)) => <>(decision[p] # "undecided")

EventualCommitLtl ==
    ((\A p \in Process: vote[p] = "YES") /\ [](crashed = {}))
        => (\A p \in Process: <>(decision[p] = "commit"))

=============================================================================