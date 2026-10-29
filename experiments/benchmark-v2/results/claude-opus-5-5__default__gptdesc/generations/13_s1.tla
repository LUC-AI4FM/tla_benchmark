------------------------------ MODULE RollingDeployment ------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Servers,      \* set of server identifiers
          Coord         \* identifier of the coordinator process

ASSUME /\ Servers # {}
       /\ Coord \notin Servers

(* --algorithm RollingDeployment
variables
    loadBalancer  = Servers,                  \* servers currently serving traffic
    startUpdate   = [s \in Servers |-> FALSE], \* coordinator's update trigger
    updated       = [s \in Servers |-> FALSE]; \* server has finished updating

fair process Updater \in Servers
begin
  WaitTrigger:
    await startUpdate[self];
  DoUpdate:
    updated[self] := TRUE;
end process;

fair process Coordinator = Coord
variables remaining = Servers, current = Coord;
begin
  Loop:
    while remaining # {} do
      with s \in remaining do
        current := s;
      end with;
  RemoveFromLB:
      loadBalancer := loadBalancer \ {current};
  Trigger:
      startUpdate[current] := TRUE;
  WaitDone:
      await updated[current];
  RestoreToLB:
      loadBalancer := loadBalancer \cup {current};
      remaining := remaining \ {current};
    end while;
end process;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES loadBalancer, startUpdate, updated, pc, remaining, current

vars == << loadBalancer, startUpdate, updated, pc, remaining, current >>

ProcSet == (Servers) \cup {Coord}

Init == (* Global variables *)
        /\ loadBalancer = Servers
        /\ startUpdate = [s \in Servers |-> FALSE]
        /\ updated = [s \in Servers |-> FALSE]
        (* Process Coordinator *)
        /\ remaining = Servers
        /\ current = Coord
        /\ pc = [self \in ProcSet |-> CASE self \in Servers -> "WaitTrigger"
                                        [] self = Coord     -> "Loop"]

WaitTrigger(self) == /\ pc[self] = "WaitTrigger"
                     /\ startUpdate[self]
                     /\ pc' = [pc EXCEPT ![self] = "DoUpdate"]
                     /\ UNCHANGED << loadBalancer, startUpdate, updated,
                                     remaining, current >>

DoUpdate(self) == /\ pc[self] = "DoUpdate"
                  /\ updated' = [updated EXCEPT ![self] = TRUE]
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << loadBalancer, startUpdate, remaining, current >>

Updater(self) == WaitTrigger(self) \/ DoUpdate(self)

Loop == /\ pc[Coord] = "Loop"
        /\ IF remaining # {}
              THEN /\ \E s \in remaining:
                        current' = s
                   /\ pc' = [pc EXCEPT ![Coord] = "RemoveFromLB"]
              ELSE /\ pc' = [pc EXCEPT ![Coord] = "Done"]
                   /\ UNCHANGED current
        /\ UNCHANGED << loadBalancer, startUpdate, updated, remaining >>

RemoveFromLB == /\ pc[Coord] = "RemoveFromLB"
                /\ loadBalancer' = loadBalancer \ {current}
                /\ pc' = [pc EXCEPT ![Coord] = "Trigger"]
                /\ UNCHANGED << startUpdate, updated, remaining, current >>

Trigger == /\ pc[Coord] = "Trigger"
           /\ startUpdate' = [startUpdate EXCEPT ![current] = TRUE]
           /\ pc' = [pc EXCEPT ![Coord] = "WaitDone"]
           /\ UNCHANGED << loadBalancer, updated, remaining, current >>

WaitDone == /\ pc[Coord] = "WaitDone"
            /\ updated[current]
            /\ pc' = [pc EXCEPT ![Coord] = "RestoreToLB"]
            /\ UNCHANGED << loadBalancer, startUpdate, updated, remaining, current >>

RestoreToLB == /\ pc[Coord] = "RestoreToLB"
               /\ loadBalancer' = (loadBalancer \cup {current})
               /\ remaining' = remaining \ {current}
               /\ pc' = [pc EXCEPT ![Coord] = "Loop"]
               /\ UNCHANGED << startUpdate, updated, current >>

Coordinator == Loop \/ RemoveFromLB \/ Trigger \/ WaitDone \/ RestoreToLB

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Coordinator
           \/ (\E self \in Servers: Updater(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Servers : WF_vars(Updater(self))
        /\ WF_vars(Coordinator)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

-----------------------------------------------------------------------------
\* Safety properties

TypeOK ==
    /\ loadBalancer \subseteq Servers
    /\ startUpdate \in [Servers -> BOOLEAN]
    /\ updated \in [Servers -> BOOLEAN]
    /\ remaining \subseteq Servers
    /\ current \in Servers \cup {Coord}
    /\ pc \in [ProcSet -> {"WaitTrigger", "DoUpdate", "Loop", "RemoveFromLB",
                           "Trigger", "WaitDone", "RestoreToLB", "Done"}]

\* Availability: at least one server always serves traffic (when |Servers| > 1)
Availability == Cardinality(Servers) > 1 => loadBalancer # {}

\* At most one server is out of the load balancer at any time
AtMostOneOut == Cardinality(Servers \ loadBalancer) <= 1

\* A server is only updated while it has been removed from the load balancer
\* (or after it has been restored once its update completed)
NoUpdateWhileServing ==
    \A s \in Servers : (pc[s] = "DoUpdate") => s \notin loadBalancer

\* An update only starts after being triggered by the coordinator
UpdateOnlyWhenTriggered ==
    \A s \in Servers : updated[s] => startUpdate[s]

\* Liveness properties
AllEventuallyUpdated == <>(\A s \in Servers : updated[s])

AllEventuallyRestored == <>(loadBalancer = Servers /\ \A s \in Servers : updated[s])

=============================================================================