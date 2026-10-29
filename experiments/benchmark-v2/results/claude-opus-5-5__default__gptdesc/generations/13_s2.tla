------------------------------ MODULE RollingDeployment ------------------------------
(***************************************************************************)
(* Rolling deployment of software across a small set of servers behind a   *)
(* load balancer.  One process per server performs the update of that      *)
(* server.  A separate coordinator process, for each server in turn,       *)
(* removes it from the load balancer, triggers its update, waits for the   *)
(* update to complete, and then restores it to the load balancer.  The     *)
(* goal is to preserve availability while the deployment is in progress.  *)
(* This is the form produced by translating a PlusCal algorithm.           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Servers,      \* the set of servers (process ids of the updaters)
          Coordinator   \* process id of the coordinator

ASSUME /\ IsFiniteSet(Servers)
       /\ Cardinality(Servers) > 1
       /\ Coordinator \notin Servers

VARIABLES lb,           \* set of servers currently in the load balancer
          trigger,      \* trigger[s] = TRUE when the update of s was requested
          updated,      \* updated[s] = TRUE when s runs the new version
          remaining,    \* servers the coordinator has not yet processed
          current,      \* server the coordinator is currently processing
          pc            \* program counter of each process

vars == << lb, trigger, updated, remaining, current, pc >>

ProcSet == Servers \cup {Coordinator}

NoServer == CHOOSE x : x \notin Servers

Init == /\ lb = Servers
        /\ trigger = [s \in Servers |-> FALSE]
        /\ updated = [s \in Servers |-> FALSE]
        /\ remaining = Servers
        /\ current = NoServer
        /\ pc = [self \in ProcSet |-> IF self \in Servers
                                        THEN "WaitTrigger"
                                        ELSE "Loop"]

(***************************************************************************)
(* Per-server update process                                               *)
(***************************************************************************)
WaitTrigger(self) == /\ pc[self] = "WaitTrigger"
                     /\ trigger[self]
                     /\ pc' = [pc EXCEPT ![self] = "DoUpdate"]
                     /\ UNCHANGED << lb, trigger, updated, remaining, current >>

DoUpdate(self) == /\ pc[self] = "DoUpdate"
                  /\ updated' = [updated EXCEPT ![self] = TRUE]
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << lb, trigger, remaining, current >>

Updater(self) == WaitTrigger(self) \/ DoUpdate(self)

(***************************************************************************)
(* Coordinator process                                                     *)
(***************************************************************************)
Loop == /\ pc[Coordinator] = "Loop"
        /\ IF remaining # {}
              THEN /\ \E s \in remaining : current' = s
                   /\ pc' = [pc EXCEPT ![Coordinator] = "Remove"]
              ELSE /\ current' = current
                   /\ pc' = [pc EXCEPT ![Coordinator] = "Done"]
        /\ UNCHANGED << lb, trigger, updated, remaining >>

Remove == /\ pc[Coordinator] = "Remove"
          /\ lb' = lb \ {current}
          /\ pc' = [pc EXCEPT ![Coordinator] = "Trigger"]
          /\ UNCHANGED << trigger, updated, remaining, current >>

Trigger == /\ pc[Coordinator] = "Trigger"
           /\ trigger' = [trigger EXCEPT ![current] = TRUE]
           /\ pc' = [pc EXCEPT ![Coordinator] = "Wait"]
           /\ UNCHANGED << lb, updated, remaining, current >>

Wait == /\ pc[Coordinator] = "Wait"
        /\ updated[current]
        /\ pc' = [pc EXCEPT ![Coordinator] = "Restore"]
        /\ UNCHANGED << lb, trigger, updated, remaining, current >>

Restore == /\ pc[Coordinator] = "Restore"
           /\ lb' = lb \cup {current}
           /\ remaining' = remaining \ {current}
           /\ pc' = [pc EXCEPT ![Coordinator] = "Loop"]
           /\ UNCHANGED << trigger, updated, current >>

coordinator == Loop \/ Remove \/ Trigger \/ Wait \/ Restore

(***************************************************************************)
(* Allow infinite stuttering to prevent deadlock on termination.           *)
(***************************************************************************)
Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == \/ coordinator
        \/ (\E self \in Servers : Updater(self))
        \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Servers : WF_vars(Updater(self))
        /\ WF_vars(coordinator)

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)
TypeOK == /\ lb \subseteq Servers
          /\ trigger \in [Servers -> BOOLEAN]
          /\ updated \in [Servers -> BOOLEAN]
          /\ remaining \subseteq Servers
          /\ current \in Servers \cup {NoServer}
          /\ pc[Coordinator] \in {"Loop", "Remove", "Trigger", "Wait", "Restore", "Done"}
          /\ \A s \in Servers : pc[s] \in {"WaitTrigger", "DoUpdate", "Done"}

\* At least one server is always serving traffic.
Availability == lb # {}

\* At most one server is out of the load balancer at any time.
AtMostOneOut == Cardinality(Servers \ lb) <= 1

\* A server is never updated while it is serving traffic.
NoUpdateWhileServing == \A s \in Servers : pc[s] = "DoUpdate" => s \notin lb

\* Updates only happen when requested.
UpdateOnlyWhenTriggered == \A s \in Servers : updated[s] => trigger[s]

\* When everything is finished, all servers are updated and back in service.
CompletionCorrect ==
    (\A self \in ProcSet : pc[self] = "Done") =>
        /\ lb = Servers
        /\ \A s \in Servers : updated[s]

(***************************************************************************)
(* Liveness                                                                *)
(***************************************************************************)
AllEventuallyUpdated == <>(\A s \in Servers : updated[s])

EventuallyAllServing == <>[](lb = Servers)

==========================================================================================