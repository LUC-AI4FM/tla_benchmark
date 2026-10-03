---- MODULE AsyncCommit ----
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Procs,  \* The set of processes
          YES,    \* The "yes" vote
          NO      \* The "no" vote

\* For model checking
ASSUME IsFiniteSet(Procs) /\ Cardinality(Procs) >= 1
ASSUME YES # NO

VARIABLES 
    vote,           \* The initial vote of each process
    crashed,        \* The set of crashed processes
    suspected,      \* suspected[p] is the set of procs suspected by p
    state,          \* The state of each process's protocol execution
    decision,       \* The decision of each process
    received_votes, \* received_votes[p] is the set of votes p has received
    messages        \* The set of messages in transit

Outcomes == {YES, NO}
Decisions == {"UNDECIDED", "COMMIT", "ABORT"}
States == {"voting", "waiting", "decided"}

\* Message format: [type |-> "VOTE", from |-> p, to |-> q, payload |-> v]
Msg == [type: {"VOTE"}, from: Procs, to: Procs, payload: Outcomes]

vars == <<vote, crashed, suspected, state, decision, received_votes, messages>>

TypeOK ==
    /\ vote \in [Procs -> Outcomes]
    /\ crashed \subseteq Procs
    /\ suspected \in [Procs -> SUBSET Procs]
    /\ state \in [Procs -> States]
    /\ decision \in [Procs -> Decisions]
    /\ received_votes \in [Procs -> SUBSET (Procs \X Outcomes)]
    /\ messages \subseteq Msg

\* Initial state predicates based on specialized conditions
AllYesInit ==
    /\ vote = [p \in Procs |-> YES]
    /\ crashed = {}
    /\ suspected = [p \in Procs |-> {}]
    /\ state = [p \in Procs |-> "voting"]
    /\ decision = [p \in Procs |-> "UNDECIDED"]
    /\ received_votes = [p \in Procs |-> {}]
    /\ messages = {}

AllNoInit ==
    /\ vote = [p \in Procs |-> NO]
    /\ crashed = {}
    /\ suspected = [p \in Procs |-> {}]
    /\ state = [p \in Procs |-> "voting"]
    /\ decision = [p \in Procs |-> "UNDECIDED"]
    /\ received_votes = [p \in Procs |-> {}]
    /\ messages = {}

Init == AllYesInit \/ AllNoInit

\* A process p can crash at any time.
Crash(p) ==
    /\ p \notin crashed
    /\ crashed' = crashed \cup {p}
    /\ UNCHANGED <<vote, suspected, state, decision, received_votes, messages>>

\* The failure detector of process p can add q to its set of suspected processes.
Suspect(p, q) ==
    /\ p \notin crashed
    /\ q \in Procs
    /\ suspected' = [suspected EXCEPT ![p] = @ \cup {q}]
    /\ UNCHANGED <<vote, crashed, state, decision, received_votes, messages>>
    
\* The failure detector of process p can remove q from its set of suspected processes.
Unsuspect(p, q) ==
    /\ p \notin crashed
    /\ q \in suspected[p]
    /\ suspected' = [suspected EXCEPT ![p] = @ \setminus {q}]
    /\ UNCHANGED <<vote, crashed, state, decision, received_votes, messages>>

\* A process p in the "voting" state broadcasts its vote.
BroadcastVote(p) ==
    /\ p \notin crashed
    /\ state[p] = "voting"
    /\ state' = [state EXCEPT ![p] = "waiting"]
    /\ messages' = messages \cup {[type |-> "VOTE", from |-> p, to |-> q, payload |-> vote[p]] : q \in Procs}
    /\ UNCHANGED <<vote, crashed, suspected, decision, received_votes>>

\* A process p receives a vote message m.
ReceiveVote(p, m) ==
    /\ p \notin crashed
    /\ m \in messages
    /\ m.to = p
    /\ m.type = "VOTE"
    /\ messages' = messages \setminus {m}
    /\ received_votes' = [received_votes EXCEPT ![p] = @ \cup {<<m.from, m.payload>>}]
    /\ UNCHANGED <<vote, crashed, suspected, state, decision>>

\* A process p decides to ABORT if it has received a NO vote.
DecideAbort(p) ==
    /\ p \notin crashed
    /\ decision[p] = "UNDECIDED"
    /\ \E <<q, v>> \in received_votes[p] : v = NO
    /\ decision' = [decision EXCEPT ![p] = "ABORT"]
    /\ state' = [state EXCEPT ![p] = "decided"]
    /\ UNCHANGED <<vote, crashed, suspected, received_votes, messages>>
    
\* A process p decides to COMMIT if it has heard from all non-suspected
\* processes and all received votes are YES.
DecideCommit(p) ==
    /\ p \notin crashed
    /\ decision[p] = "UNDECIDED"
    /\ LET voters == {q : <<q, v>> \in received_votes[p]} IN
         /\ Procs = voters \cup suspected[p]
         /\ \A <<q, v>> \in received_votes[p] : v = YES
    /\ decision' = [decision EXCEPT ![p] = "COMMIT"]
    /\ state' = [state EXCEPT ![p] = "decided"]
    /\ UNCHANGED <<vote, crashed, suspected, received_votes, messages>>

\* A process action is one of the protocol steps a process can take.
ProcessAction(p) ==
    \/ BroadcastVote(p)
    \/ (\E m \in messages : ReceiveVote(p, m))
    \/ DecideAbort(p)
    \/ DecideCommit(p)

\* An environment action is a crash or a change in suspicions.
EnvironmentAction ==
    \/ (\E p \in Procs : Crash(p))
    \/ (\E p, q \in Procs : Suspect(p, q))
    \/ (\E p, q \in Procs : Unsuspect(p, q))

Next ==
    \/ (\E p \in Procs : ProcessAction(p))
    \/ EnvironmentAction
    \/ UNCHANGED vars \* Stuttering step

Fairness == /\ \A p \in Procs : WF_vars(ProcessAction(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\*=============================================================================