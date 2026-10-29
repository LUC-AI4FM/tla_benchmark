---------------------------- MODULE RollingUpdate ----------------------------
(***************************************************************************)
(* Rolling update of a small cluster of identical servers behind a load   *)
(* balancer.                                                               *)
(*                                                                         *)
(* Each server runs either the old version or the new version, or it is   *)
(* in the intermediate UPDATING state. An UPDATING server cannot serve     *)
(* requests.                                                               *)
(*                                                                         *)
(* The orchestrator does the following:                                    *)
(*  - It removes one or more old servers from the load balancer. At least *)
(*    one server always remains in the load balancer.                      *)
(*  - It authorises the removed servers to update. Those servers then     *)
(*    start and finish their updates on their own.                         *)
(*  - It returns removed servers to the load balancer only after their    *)
(*    updates have finished.                                               *)
(*                                                                         *)
(* Returning updated servers works in one of two ways:                     *)
(*  - If the load-balanced set already runs the new version, the servers  *)
(*    are simply added to it.                                              *)
(*  - If the load-balanced set still runs the old version, the            *)
(*    orchestrator performs an atomic cut-over. The returned new servers  *)
(*    become the whole load-balanced set. The old servers that were       *)
(*    serving are removed and scheduled for update.                        *)
(* In both cases the load-balanced set stays version-homogeneous and is   *)
(* never empty.                                                            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

\* Model parameters: the set of servers and the intermediate state.
Servers  == {"s1", "s2", "s3"}
UPDATING == "updating"

OLD == "old"
NEW == "new"

VersionStates == {OLD, NEW, UPDATING}

VARIABLES
    version,   \* version[s] \in {OLD, NEW, UPDATING}
    inLB,      \* set of servers currently receiving traffic
    pending    \* servers removed by the orchestrator, awaiting update/return

vars == <<version, inLB, pending>>

TypeOK ==
    /\ version \in [Servers -> VersionStates]
    /\ inLB \subseteq Servers
    /\ pending \subseteq Servers

Init ==
    /\ version = [s \in Servers |-> OLD]
    /\ inLB = Servers
    /\ pending = {}

-----------------------------------------------------------------------------
(* Orchestrator actions *)

\* Remove a nonempty set of old servers from the load balancer.
\* At least one server must keep serving.
RemoveServers(S) ==
    /\ S # {}
    /\ S \subseteq inLB
    /\ inLB \ S # {}
    /\ \A s \in S : version[s] = OLD
    /\ inLB' = inLB \ S
    /\ pending' = pending \cup S
    /\ UNCHANGED version

\* Return a nonempty set of removed servers whose updates have all finished.
ReturnServers(S) ==
    /\ S # {}
    /\ S \subseteq pending
    /\ \A s \in S : version[s] = NEW            \* must wait for update completion
    /\ IF \A t \in inLB : version[t] = NEW
          THEN \* LB already on new version: simply add.
               /\ inLB' = inLB \cup S
               /\ pending' = pending \ S
          ELSE \* LB still on old version: atomic cut-over.
               /\ inLB' = S
               /\ pending' = (pending \ S) \cup inLB
    /\ UNCHANGED version

-----------------------------------------------------------------------------
(* Server actions *)

\* A removed server that is allowed to update starts updating.
StartUpdate(s) ==
    /\ s \in pending
    /\ s \notin inLB
    /\ version[s] = OLD
    /\ version' = [version EXCEPT ![s] = UPDATING]
    /\ UNCHANGED <<inLB, pending>>

\* An updating server finishes and marks itself updated.
FinishUpdate(s) ==
    /\ version[s] = UPDATING
    /\ version' = [version EXCEPT ![s] = NEW]
    /\ UNCHANGED <<inLB, pending>>

-----------------------------------------------------------------------------

Done ==
    /\ \A s \in Servers : version[s] = NEW
    /\ inLB = Servers
    /\ pending = {}

Terminated == Done /\ UNCHANGED vars

OrchRemove == \E S \in SUBSET Servers : RemoveServers(S)
OrchReturn == \E S \in SUBSET Servers : ReturnServers(S)

Next ==
    \/ OrchRemove
    \/ OrchReturn
    \/ \E s \in Servers : StartUpdate(s)
    \/ \E s \in Servers : FinishUpdate(s)
    \/ Terminated

Fairness ==
    /\ WF_vars(OrchRemove)
    /\ WF_vars(OrchReturn)
    /\ \A s \in Servers : WF_vars(StartUpdate(s))
    /\ \A s \in Servers : WF_vars(FinishUpdate(s))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties *)

Serving(s) == version[s] # UPDATING

\* Safety: the load-balanced set is version-homogeneous and contains no
\* intermediate (non-serving) servers.
VersionHomogeneous ==
    /\ \A s, t \in inLB : version[s] = version[t]
    /\ \A s \in inLB : Serving(s)

\* Zero downtime: at least one serving server is always load-balanced.
ZeroDowntime == \E s \in inLB : Serving(s)

\* Servers receiving traffic are never also scheduled for update.
NoUpdatingInLB == \A s \in inLB : s \notin pending /\ version[s] # UPDATING

\* Every server that starts updating eventually finishes.
UpdateFinishes == \A s \in Servers : (version[s] = UPDATING) ~> (version[s] = NEW)

\* The whole procedure eventually completes.
EventuallyComplete == <>[]Done

=============================================================================