------------------------------ MODULE RollingDeployment ------------------------------
(***************************************************************************)
(* Rolling deployment of software across a small set of servers behind a   *)
(* load balancer.                                                          *)
(*                                                                         *)
(* - One "Update" process per server waits until the coordinator asks it   *)
(*   to update, then installs the new version.                             *)
(* - A single "Coordinator" process handles one server at a time. It       *)
(*   removes the server from the load balancer, triggers its update, waits *)
(*   for the update to complete, and then restores the server to the load  *)
(*   balancer.                                                             *)
(*                                                                         *)
(* The goal is that availability is preserved throughout: at least one     *)
(* server is always in service behind the load balancer.                   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Servers          \* e.g. {1, 2, 3}

Coordinator == 0

ASSUME /\ Servers \subseteq (Nat \ {0})
       /\ Cardinality(Servers) >= 2

(***************************************************************************
--algorithm RollingDeployment
variables
    loadBalancer     = Servers,
    updated          = [s \in Servers |-> FALSE],
    updateRequested  = [s \in Servers |-> FALSE];

fair process Update \in Servers
begin
  WaitRequest:
    await updateRequested[self];
  DoUpdate:
    updated[self] := TRUE;
    updateRequested[self] := FALSE;
end process;

fair process Coord = Coordinator
variables remaining = Servers, current = Coordinator;
begin
  Loop:
    while remaining # {} do
      current := CHOOSE s \in remaining : TRUE;
      remaining := remaining \ {current};
  Remove:
      loadBalancer := loadBalancer \ {current};
  Trigger:
      updateRequested[current] := TRUE;
  WaitDone:
      await updated[current];
  Restore:
      loadBalancer := loadBalancer \cup {current};
    end while;
end process;
end algorithm;
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES loadBalancer, updated, updateRequested, pc, remaining, current

vars == << loadBalancer, updated, updateRequested, pc, remaining, current >>

ProcSet == Servers \cup {Coordinator}

Init == /\ loadBalancer = Servers
        /\ updated = [s \in Servers |-> FALSE]
        /\ updateRequested = [s \in Servers |-> FALSE]
        /\ remaining = Servers
        /\ current = Coordinator
        /\ pc = [self \in ProcSet |-> CASE self \in Servers -> "WaitRequest"
                                        [] self = Coordinator -> "Loop"]

WaitRequest(self) == /\ pc[self] = "WaitRequest"
                     /\ updateRequested[self]
                     /\ pc' = [pc EXCEPT ![self] = "DoUpdate"]
                     /\ UNCHANGED << loadBalancer, updated, updateRequested,
                                     remaining, current >>

DoUpdate(self) == /\ pc[self] = "DoUpdate"
                  /\ updated' = [updated EXCEPT ![self] = TRUE]
                  /\ updateRequested' = [updateRequested EXCEPT ![self] = FALSE]
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << loadBalancer, remaining, current >>

Update(self) == WaitRequest(self) \/ DoUpdate(self)

Loop == /\ pc[Coordinator] = "Loop"
        /\ IF remaining # {}
              THEN /\ current' = (CHOOSE s \in remaining : TRUE)
                   /\ remaining' = remaining \ {current'}
                   /\ pc' = [pc EXCEPT ![Coordinator] = "Remove"]
              ELSE /\ pc' = [pc EXCEPT ![Coordinator] = "Done"]
                   /\ UNCHANGED << remaining, current >>
        /\ UNCHANGED << loadBalancer, updated, updateRequested >>

Remove == /\ pc[Coordinator] = "Remove"
          /\ loadBalancer' = loadBalancer \ {current}
          /\ pc' = [pc EXCEPT ![Coordinator] = "Trigger"]
          /\ UNCHANGED << updated, updateRequested, remaining, current >>

Trigger == /\ pc[Coordinator] = "Trigger"
           /\ updateRequested' = [updateRequested EXCEPT ![current] = TRUE]
           /\ pc' = [pc EXCEPT ![Coordinator] = "WaitDone"]
           /\ UNCHANGED << loadBalancer, updated, remaining, current >>

WaitDone == /\ pc[Coordinator] = "WaitDone"
            /\ updated[current]
            /\ pc' = [pc EXCEPT ![Coordinator] = "Restore"]
            /\ UNCHANGED << loadBalancer, updated, updateRequested,
                            remaining, current >>

Restore == /\ pc[Coordinator] = "Restore"
           /\ loadBalancer' = loadBalancer \cup {current}
           /\ pc' = [pc EXCEPT ![Coordinator] = "Loop"]
           /\ UNCHANGED << updated, updateRequested, remaining, current >>

Coord == Loop \/ Remove \/ Trigger \/ WaitDone \/ Restore

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == Coord
           \/ (\E self \in Servers : Update(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Servers : WF_vars(Update(self))
        /\ WF_vars(Coord)

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

\* END TRANSLATION

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ loadBalancer \subseteq Servers
    /\ updated \in [Servers -> BOOLEAN]
    /\ updateRequested \in [Servers -> BOOLEAN]
    /\ remaining \subseteq Servers
    /\ current \in Servers \cup {Coordinator}
    /\ pc \in [ProcSet -> {"WaitRequest", "DoUpdate", "Loop", "Remove",
                           "Trigger", "WaitDone", "Restore", "Done"}]

\* Availability: at least one server is always serving traffic.
Availability == loadBalancer # {}

\* A server is never being updated while it is in the load balancer.
NoUpdateWhileServing ==
    \A s \in Servers : pc[s] = "DoUpdate" => s \notin loadBalancer

\* At most one server is out of the load balancer at any time.
AtMostOneOut == Cardinality(Servers \ loadBalancer) <= 1

\* Once the coordinator is finished, every server is updated and in service.
DeploymentComplete ==
    pc[Coordinator] = "Done" =>
        /\ \A s \in Servers : updated[s]
        /\ loadBalancer = Servers

(* Liveness properties *)

AllEventuallyUpdated == <>(\A s \in Servers : updated[s])

EventuallyFullyRestored == <>[](loadBalancer = Servers /\ \A s \in Servers : updated[s])

=============================================================================