---------------------------- MODULE RollingDeployment ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT Servers

VARIABLES
    serverVersion,      \* serverVersion[s] \in {"old", "new"} - current software version
    serverStatus,       \* serverStatus[s] \in {"active", "draining", "updating", "ready"} - server state
    lbPool,             \* Set of servers currently in load balancer pool
    coordState,         \* Coordinator state
    coordTarget,        \* Current server being updated by coordinator
    updateQueue,        \* Queue of servers to update
    pc                  \* Program counter for processes

vars == <<serverVersion, serverStatus, lbPool, coordState, coordTarget, updateQueue, pc>>

ServerProcs == Servers
CoordProc == "coordinator"
AllProcs == ServerProcs \cup {CoordProc}

TypeOK ==
    /\ serverVersion \in [Servers -> {"old", "new"}]
    /\ serverStatus \in [Servers -> {"active", "draining", "updating", "ready"}]
    /\ lbPool \subseteq Servers
    /\ coordState \in {"idle", "selecting", "draining", "triggering", "waiting", "restoring", "done"}
    /\ coordTarget \in Servers \cup {CHOOSE x : x \notin Servers}
    /\ updateQueue \subseteq Servers
    /\ pc \in [AllProcs -> {"ServerIdle", "ServerUpdating", "ServerDone", 
                            "CoordStart", "CoordSelect", "CoordDrain", 
                            "CoordTrigger", "CoordWait", "CoordRestore", 
                            "CoordCheck", "CoordDone"}]

Init ==
    /\ serverVersion = [s \in Servers |-> "old"]
    /\ serverStatus = [s \in Servers |-> "active"]
    /\ lbPool = Servers
    /\ coordState = "idle"
    /\ coordTarget = CHOOSE x : x \notin Servers
    /\ updateQueue = Servers
    /\ pc = [p \in AllProcs |-> IF p = CoordProc THEN "CoordStart" ELSE "ServerIdle"]

\* Server process actions
ServerStartUpdate(s) ==
    /\ pc[s] = "ServerIdle"
    /\ serverStatus[s] = "updating"
    /\ pc' = [pc EXCEPT ![s] = "ServerUpdating"]
    /\ UNCHANGED <<serverVersion, serverStatus, lbPool, coordState, coordTarget, updateQueue>>

ServerCompleteUpdate(s) ==
    /\ pc[s] = "ServerUpdating"
    /\ serverVersion' = [serverVersion EXCEPT ![s] = "new"]
    /\ serverStatus' = [serverStatus EXCEPT ![s] = "ready"]
    /\ pc' = [pc EXCEPT ![s] = "ServerDone"]
    /\ UNCHANGED <<lbPool, coordState, coordTarget, updateQueue>>

\* Coordinator process actions
CoordStart ==
    /\ pc[CoordProc] = "CoordStart"
    /\ coordState' = "selecting"
    /\ pc' = [pc EXCEPT ![CoordProc] = "CoordSelect"]
    /\ UNCHANGED <<serverVersion, serverStatus, lbPool, coordTarget, updateQueue>>

CoordSelect ==
    /\ pc[CoordProc] = "CoordSelect"
    /\ IF updateQueue # {}
       THEN /\ coordTarget' \in updateQueue
            /\ updateQueue' = updateQueue \ {coordTarget'}
            /\ coordState' = "draining"
            /\ pc' = [pc EXCEPT ![CoordProc] = "CoordDrain"]
            /\ UNCHANGED <<serverVersion, serverStatus, lbPool>>
       ELSE /\ coordState' = "done"
            /\ pc' = [pc EXCEPT ![CoordProc] = "CoordDone"]
            /\ UNCHANGED <<serverVersion, serverStatus, lbPool, coordTarget, updateQueue>>

CoordDrain ==
    /\ pc[CoordProc] = "CoordDrain"
    /\ lbPool' = lbPool \ {coordTarget}
    /\ serverStatus' = [serverStatus EXCEPT ![coordTarget] = "draining"]
    /\ coordState' = "triggering"
    /\ pc' = [pc EXCEPT ![CoordProc] = "CoordTrigger"]
    /\ UNCHANGED <<serverVersion, coordTarget, updateQueue>>

CoordTrigger ==
    /\ pc[CoordProc] = "CoordTrigger"
    /\ serverStatus' = [serverStatus EXCEPT ![coordTarget] = "updating"]
    /\ coordState' = "waiting"
    /\ pc' = [pc EXCEPT ![CoordProc] = "CoordWait"]
    /\ UNCHANGED <<serverVersion, lbPool, coordTarget, updateQueue>>

CoordWait ==
    /\ pc[CoordProc] = "CoordWait"
    /\ serverStatus[coordTarget] = "ready"
    /\ coordState' = "restoring"
    /\ pc' = [pc EXCEPT ![CoordProc] = "CoordRestore"]
    /\ UNCHANGED <<serverVersion, serverStatus, lbPool, coordTarget, updateQueue>>

CoordRestore ==
    /\ pc[CoordProc] = "CoordRestore"
    /\ lbPool' = lbPool \cup {coordTarget}
    /\ serverStatus' = [serverStatus EXCEPT ![coordTarget] = "active"]
    /\ coordState' = "selecting"
    /\ pc' = [pc EXCEPT ![CoordProc] = "CoordSelect"]
    /\ UNCHANGED <<serverVersion, coordTarget, updateQueue>>

CoordDone ==
    /\ pc[CoordProc] = "CoordDone"
    /\ UNCHANGED vars

ServerDone(s) ==
    /\ pc[s] = "ServerDone"
    /\ UNCHANGED vars

\* Combined next state relation
ServerNext(s) ==
    \/ ServerStartUpdate(s)
    \/ ServerCompleteUpdate(s)
    \/ ServerDone(s)

CoordNext ==
    \/ CoordStart
    \/ CoordSelect
    \/ CoordDrain
    \/ CoordTrigger
    \/ CoordWait
    \/ CoordRestore
    \/ CoordDone

Next ==
    \/ \E s \in Servers : ServerNext(s)
    \/ CoordNext

\* Fairness conditions
ServerFairness == \A s \in Servers : WF_vars(ServerNext(s))
CoordFairness == WF_vars(CoordNext)

\* The main specification
Spec == Init /\ [][Next]_vars /\ ServerFairness /\ CoordFairness

\* Termination: all processes eventually complete
Termination ==
    /\ pc[CoordProc] = "CoordDone"
    /\ \A s \in Servers : pc[s] = "ServerDone"

\* Temporal property: system eventually terminates
EventualTermination == <>Termination

\* Availability invariant: at least one server is always in the load balancer pool
\* (except possibly in edge cases during transitions)
Availability == Cardinality(Servers) > 1 => lbPool # {}

=============================================================================