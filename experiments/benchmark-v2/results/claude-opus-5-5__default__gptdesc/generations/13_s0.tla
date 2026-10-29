--------------------------- MODULE RollingDeployment ---------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Servers, Coordinator

ASSUME /\ IsFiniteSet(Servers)
       /\ Cardinality(Servers) >= 2
       /\ Coordinator \notin Servers

(* --algorithm RollingDeployment
variables
    inLB    = [s \in Servers |-> TRUE],
    trigger = [s \in Servers |-> FALSE],
    updated = [s \in Servers |-> FALSE];

fair process Updater \in Servers
begin
  WaitTrigger:
    await trigger[self];
  DoUpdate:
    updated[self] := TRUE;
    trigger[self] := FALSE;
end process;

fair process Coord = Coordinator
variables remaining = Servers, cur = CHOOSE s \in Servers : TRUE;
begin
  Loop:
    while remaining # {} do
      with s \in remaining do
        cur := s;
        remaining := remaining \ {s};
      end with;
  Remove:
      inLB[cur] := FALSE;
  Trigger:
      trigger[cur] := TRUE;
  Wait:
      await updated[cur];
  Restore:
      inLB[cur] := TRUE;
    end while;
end process;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES inLB, trigger, updated, pc, remaining, cur

vars == << inLB, trigger, updated, pc, remaining, cur >>

ProcSet == Servers \cup {Coordinator}

Init == /\ inLB = [s \in Servers |-> TRUE]
        /\ trigger = [s \in Servers |-> FALSE]
        /\ updated = [s \in Servers |-> FALSE]
        /\ remaining = Servers
        /\ cur = CHOOSE s \in Servers : TRUE
        /\ pc = [self \in ProcSet |-> CASE self \in Servers -> "WaitTrigger"
                                        [] self = Coordinator -> "Loop"]

WaitTrigger(self) == /\ pc[self] = "WaitTrigger"
                     /\ trigger[self]
                     /\ pc' = [pc EXCEPT ![self] = "DoUpdate"]
                     /\ UNCHANGED << inLB, trigger, updated, remaining, cur >>

DoUpdate(self) == /\ pc[self] = "DoUpdate"
                  /\ updated' = [updated EXCEPT ![self] = TRUE]
                  /\ trigger' = [trigger EXCEPT ![self] = FALSE]
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << inLB, remaining, cur >>

Updater(self) == WaitTrigger(self) \/ DoUpdate(self)

Loop == /\ pc[Coordinator] = "Loop"
        /\ IF remaining # {}
              THEN /\ \E s \in remaining :
                        /\ cur' = s
                        /\ remaining' = remaining \ {s}
                   /\ pc' = [pc EXCEPT ![Coordinator] = "Remove"]
              ELSE /\ pc' = [pc EXCEPT ![Coordinator] = "Done"]
                   /\ UNCHANGED << remaining, cur >>
        /\ UNCHANGED << inLB, trigger, updated >>

Remove == /\ pc[Coordinator] = "Remove"
          /\ inLB' = [inLB EXCEPT ![cur] = FALSE]
          /\ pc' = [pc EXCEPT ![Coordinator] = "Trigger"]
          /\ UNCHANGED << trigger, updated, remaining, cur >>

Trigger == /\ pc[Coordinator] = "Trigger"
           /\ trigger' = [trigger EXCEPT ![cur] = TRUE]
           /\ pc' = [pc EXCEPT ![Coordinator] = "Wait"]
           /\ UNCHANGED << inLB, updated, remaining, cur >>

Wait == /\ pc[Coordinator] = "Wait"
        /\ updated[cur]
        /\ pc' = [pc EXCEPT ![Coordinator] = "Restore"]
        /\ UNCHANGED << inLB, trigger, updated, remaining, cur >>

Restore == /\ pc[Coordinator] = "Restore"
           /\ inLB' = [inLB EXCEPT ![cur] = TRUE]
           /\ pc' = [pc EXCEPT ![Coordinator] = "Loop"]
           /\ UNCHANGED << trigger, updated, remaining, cur >>

Coord == Loop \/ Remove \/ Trigger \/ Wait \/ Restore

\* Allow infinite stuttering to prevent deadlock on termination.
Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == \/ Coord
        \/ (\E self \in Servers : Updater(self))
        \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Servers : WF_vars(Updater(self))
        /\ WF_vars(Coord)

Termination == <>(\A self \in ProcSet : pc[self] = "Done")
\* END TRANSLATION

-----------------------------------------------------------------------------
\* Safety properties

TypeOK ==
    /\ inLB \in [Servers -> BOOLEAN]
    /\ trigger \in [Servers -> BOOLEAN]
    /\ updated \in [Servers -> BOOLEAN]
    /\ remaining \subseteq Servers
    /\ cur \in Servers
    /\ pc \in [ProcSet -> {"WaitTrigger", "DoUpdate", "Loop", "Remove",
                           "Trigger", "Wait", "Restore", "Done"}]

\* Availability: at least one server is always serving traffic.
Availability == \E s \in Servers : inLB[s]

\* At most one server is out of the load balancer at any time.
AtMostOneOut == \A s1, s2 \in Servers :
                    (~inLB[s1] /\ ~inLB[s2]) => s1 = s2

\* A server is only ever updated while removed from the load balancer.
UpdateOnlyWhenOut == \A s \in Servers :
                        pc[s] = "DoUpdate" => ~inLB[s]

SafetyInvariant == TypeOK /\ Availability /\ AtMostOneOut /\ UpdateOnlyWhenOut

\* Liveness properties

AllEventuallyUpdated == <>(\A s \in Servers : updated[s])

AllEventuallyRestored == <>[](\A s \in Servers : inLB[s] /\ updated[s])

=============================================================================