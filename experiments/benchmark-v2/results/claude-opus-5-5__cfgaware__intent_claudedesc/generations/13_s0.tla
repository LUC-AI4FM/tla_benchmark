---------------------------- MODULE RollingDeploy ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANT UPDATING

Servers == {1, 2, 3}

FirstServer == 1

Versions == {FALSE, UPDATING, TRUE}

VARIABLES
    updated,        \* updated[s] \in {FALSE, UPDATING, TRUE}
    lb,             \* set of servers behind the load balancer
    signal,         \* signal[s] = TRUE once the coordinator asks s to update
    pc              \* coordinator program counter

vars == << updated, lb, signal, pc >>

TypeOK ==
    /\ updated \in [Servers -> Versions]
    /\ lb \subseteq Servers
    /\ signal \in [Servers -> BOOLEAN]
    /\ pc \in {"Phase1", "Phase2", "Phase3", "Done"}

Init ==
    /\ updated = [s \in Servers |-> FALSE]
    /\ lb = Servers
    /\ signal = [s \in Servers |-> FALSE]
    /\ pc = "Phase1"

\* Coordinator, phase 1: take one server out of the load balancer and
\* signal it to update.
Phase1 ==
    /\ pc = "Phase1"
    /\ lb' = Servers \ {FirstServer}
    /\ signal' = [signal EXCEPT ![FirstServer] = TRUE]
    /\ pc' = "Phase2"
    /\ UNCHANGED updated

\* Coordinator, phase 2: once the first server has finished updating,
\* switch the load balancer to it and update the remaining servers.
Phase2 ==
    /\ pc = "Phase2"
    /\ updated[FirstServer] = TRUE
    /\ lb' = {FirstServer}
    /\ signal' = [s \in Servers |-> TRUE]
    /\ pc' = "Phase3"
    /\ UNCHANGED updated

\* Coordinator, phase 3: once all servers are updated, put them all
\* back behind the load balancer.
Phase3 ==
    /\ pc = "Phase3"
    /\ \A s \in Servers : updated[s] = TRUE
    /\ lb' = Servers
    /\ pc' = "Done"
    /\ UNCHANGED << updated, signal >>

Coordinator == Phase1 \/ Phase2 \/ Phase3

\* A signaled server begins updating.
StartUpdate(s) ==
    /\ signal[s]
    /\ updated[s] = FALSE
    /\ updated' = [updated EXCEPT ![s] = UPDATING]
    /\ UNCHANGED << lb, signal, pc >>

\* An updating server finishes with the new version.
FinishUpdate(s) ==
    /\ updated[s] = UPDATING
    /\ updated' = [updated EXCEPT ![s] = TRUE]
    /\ UNCHANGED << lb, signal, pc >>

Server(s) == StartUpdate(s) \/ FinishUpdate(s)

Terminating ==
    /\ pc = "Done"
    /\ \A s \in Servers : updated[s] = TRUE
    /\ UNCHANGED vars

Next ==
    \/ Coordinator
    \/ \E s \in Servers : Server(s)
    \/ Terminating

Fairness ==
    /\ WF_vars(Coordinator)
    /\ \A s \in Servers : WF_vars(Server(s))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Correctness properties

ZeroDowntime ==
    \E s \in lb : updated[s] # UPDATING

SameVersion ==
    \A s1, s2 \in lb : updated[s1] = updated[s2]

Termination ==
    <>(pc = "Done" /\ \A s \in Servers : updated[s] = TRUE)

=============================================================================