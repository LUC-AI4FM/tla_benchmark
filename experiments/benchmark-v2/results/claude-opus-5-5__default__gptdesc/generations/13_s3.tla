---------------------------- MODULE RollingDeployment ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Servers, NoServer

ASSUME /\ IsFiniteSet(Servers)
       /\ Cardinality(Servers) >= 2
       /\ NoServer \notin Servers

(* --algorithm RollingDeployment
variables
    lb        = Servers,
    version   = [s \in Servers |-> "old"],
    request   = NoServer,
    done      = FALSE,
    remaining = Servers;

process updater = "updater"
begin
  UWait:
    await request # NoServer \/ pc["coord"] = "Done";
    if request # NoServer then
  UUpdate:
      version[request] := "new";
      done := TRUE;
      request := NoServer;
      goto UWait;
    end if;
end process;

process coordinator = "coord"
variable cur = NoServer;
begin
  CLoop:
    while remaining # {} do
      with s \in remaining do cur := s; end with;
  CRemove:
      lb := lb \ {cur};
  CTrigger:
      done := FALSE;
      request := cur;
  CWait:
      await done;
  CRestore:
      lb := lb \cup {cur};
      remaining := remaining \ {cur};
      done := FALSE;
      cur := NoServer;
    end while;
end process;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES lb, version, request, done, remaining, pc, cur

vars == << lb, version, request, done, remaining, pc, cur >>

ProcSet == {"updater"} \cup {"coord"}

Init == /\ lb = Servers
        /\ version = [s \in Servers |-> "old"]
        /\ request = NoServer
        /\ done = FALSE
        /\ remaining = Servers
        /\ cur = NoServer
        /\ pc = [self \in ProcSet |-> CASE self = "updater" -> "UWait"
                                        [] self = "coord"   -> "CLoop"]

UWait == /\ pc["updater"] = "UWait"
         /\ request # NoServer \/ pc["coord"] = "Done"
         /\ IF request # NoServer
               THEN pc' = [pc EXCEPT !["updater"] = "UUpdate"]
               ELSE pc' = [pc EXCEPT !["updater"] = "Done"]
         /\ UNCHANGED << lb, version, request, done, remaining, cur >>

UUpdate == /\ pc["updater"] = "UUpdate"
           /\ version' = [version EXCEPT ![request] = "new"]
           /\ done' = TRUE
           /\ request' = NoServer
           /\ pc' = [pc EXCEPT !["updater"] = "UWait"]
           /\ UNCHANGED << lb, remaining, cur >>

updater == UWait \/ UUpdate

CLoop == /\ pc["coord"] = "CLoop"
         /\ IF remaining # {}
               THEN /\ \E s \in remaining : cur' = s
                    /\ pc' = [pc EXCEPT !["coord"] = "CRemove"]
               ELSE /\ pc' = [pc EXCEPT !["coord"] = "Done"]
                    /\ cur' = cur
         /\ UNCHANGED << lb, version, request, done, remaining >>

CRemove == /\ pc["coord"] = "CRemove"
           /\ lb' = lb \ {cur}
           /\ pc' = [pc EXCEPT !["coord"] = "CTrigger"]
           /\ UNCHANGED << version, request, done, remaining, cur >>

CTrigger == /\ pc["coord"] = "CTrigger"
            /\ done' = FALSE
            /\ request' = cur
            /\ pc' = [pc EXCEPT !["coord"] = "CWait"]
            /\ UNCHANGED << lb, version, remaining, cur >>

CWait == /\ pc["coord"] = "CWait"
         /\ done
         /\ pc' = [pc EXCEPT !["coord"] = "CRestore"]
         /\ UNCHANGED << lb, version, request, done, remaining, cur >>

CRestore == /\ pc["coord"] = "CRestore"
            /\ lb' = lb \cup {cur}
            /\ remaining' = remaining \ {cur}
            /\ done' = FALSE
            /\ cur' = NoServer
            /\ pc' = [pc EXCEPT !["coord"] = "CLoop"]
            /\ UNCHANGED << version, request >>

coordinator == CLoop \/ CRemove \/ CTrigger \/ CWait \/ CRestore

Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == updater \/ coordinator \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(updater)
        /\ WF_vars(coordinator)

Termination == <>(\A self \in ProcSet : pc[self] = "Done")
\* END TRANSLATION

-----------------------------------------------------------------------------
\* Safety properties

TypeOK ==
    /\ lb \subseteq Servers
    /\ version \in [Servers -> {"old", "new"}]
    /\ request \in Servers \cup {NoServer}
    /\ done \in BOOLEAN
    /\ remaining \subseteq Servers
    /\ cur \in Servers \cup {NoServer}

\* Service stays available: at least one server is always in the load balancer
Availability == lb # {}

\* At most one server is out of rotation at any time
AtMostOneOut == Cardinality(Servers \ lb) <= 1

\* A server is never updated while it is serving traffic
UpdatingNotInLB == request # NoServer => request \notin lb

\* Servers no longer pending have been updated
FinishedAreNew == \A s \in Servers \ remaining : version[s] = "new"

\* On completion, every server runs the new version and is back in service
DoneCorrect ==
    (\A self \in ProcSet : pc[self] = "Done") =>
        /\ \A s \in Servers : version[s] = "new"
        /\ lb = Servers

\* Liveness properties
AllUpdated == <>(\A s \in Servers : version[s] = "new")

AllRestored == <>[](lb = Servers)

=============================================================================