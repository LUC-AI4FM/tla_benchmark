------------------------------ MODULE RollingDeployment ------------------------------
(***************************************************************************)
(* Rolling deployment of a cluster of three servers behind a load         *)
(* balancer.                                                              *)
(*                                                                         *)
(* The coordinator upgrades the servers in two phases:                     *)
(*   Phase 1: The load balancer is reduced to the original server only.    *)
(*            The other servers are taken out of the load balancer and are *)
(*            signaled to update.                                          *)
(*   Phase 2: Once the remaining servers are updated, the load balancer is *)
(*            switched to the newly updated servers. The original server   *)
(*            is then signaled to complete its update.                     *)
(*   Finish:  Once the original server is updated, all servers are put     *)
(*            back behind the load balancer.                               *)
(*                                                                         *)
(* Each signaled server goes from "old" through an intermediate            *)
(* "updating" state and ends at "new".                                     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

Servers == {1, 2, 3}
Orig    == 1                     \* the original server, updated last
Others  == Servers \ {Orig}

Versions == {"old", "updating", "new"}
Phases   == {"start", "phase1", "phase2", "done"}

VARIABLES
    lb,       \* set of servers currently behind the load balancer
    ver,      \* ver[s] : software state of server s
    signal,   \* set of servers that have been signaled to update
    phase     \* coordinator phase

vars == <<lb, ver, signal, phase>>

TypeOK ==
    /\ lb \subseteq Servers
    /\ ver \in [Servers -> Versions]
    /\ signal \subseteq Servers
    /\ phase \in Phases

Init ==
    /\ lb = Servers
    /\ ver = [s \in Servers |-> "old"]
    /\ signal = {}
    /\ phase = "start"

(***************************************************************************)
(* Coordinator actions                                                     *)
(***************************************************************************)

\* Phase 1: keep only the original server in the load balancer and
\* signal the other servers to update.
StartPhase1 ==
    /\ phase = "start"
    /\ lb' = {Orig}
    /\ signal' = signal \cup Others
    /\ phase' = "phase1"
    /\ UNCHANGED ver

\* Phase 2: once the remaining servers are updated, switch the load
\* balancer to the newly updated servers and signal the original server.
StartPhase2 ==
    /\ phase = "phase1"
    /\ \A s \in Others : ver[s] = "new"
    /\ lb' = Others
    /\ signal' = signal \cup {Orig}
    /\ phase' = "phase2"
    /\ UNCHANGED ver

\* Completion: once the original server is updated, restore all servers
\* to the load balancer.
FinishDeploy ==
    /\ phase = "phase2"
    /\ ver[Orig] = "new"
    /\ lb' = Servers
    /\ phase' = "done"
    /\ UNCHANGED <<ver, signal>>

Coordinator == StartPhase1 \/ StartPhase2 \/ FinishDeploy

(***************************************************************************)
(* Server actions                                                          *)
(***************************************************************************)

BeginUpdate(s) ==
    /\ s \in signal
    /\ ver[s] = "old"
    /\ ver' = [ver EXCEPT ![s] = "updating"]
    /\ UNCHANGED <<lb, signal, phase>>

EndUpdate(s) ==
    /\ ver[s] = "updating"
    /\ ver' = [ver EXCEPT ![s] = "new"]
    /\ signal' = signal \ {s}
    /\ UNCHANGED <<lb, phase>>

Server(s) == BeginUpdate(s) \/ EndUpdate(s)

(***************************************************************************)
(* Termination stuttering                                                  *)
(***************************************************************************)

Terminated ==
    /\ phase = "done"
    /\ UNCHANGED vars

Next ==
    \/ Coordinator
    \/ \E s \in Servers : Server(s)
    \/ Terminated

Fairness ==
    /\ WF_vars(Coordinator)
    /\ \A s \in Servers : WF_vars(Server(s))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

\* Zero downtime: the load balancer always contains at least one server
\* that is not mid-update.
ZeroDowntime ==
    \E s \in lb : ver[s] # "updating"

\* Same version: all servers behind the load balancer run the same version.
SameVersion ==
    \A s, t \in lb : ver[s] = ver[t]

Safety == TypeOK /\ ZeroDowntime /\ SameVersion

(***************************************************************************)
(* Liveness property                                                       *)
(***************************************************************************)

AllUpdated == \A s \in Servers : ver[s] = "new"

\* Termination: the deployment always eventually completes with all
\* servers updated.
Termination ==
    <>(phase = "done" /\ AllUpdated /\ lb = Servers)

THEOREM Spec => [](TypeOK /\ ZeroDowntime /\ SameVersion)
THEOREM Spec => Termination
=====================================================================================