---------------------------- MODULE RollingDeployment ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANT UPDATING

Servers == 1..3
Coordinator == 0

(* --algorithm RollingDeployment
variables
    status = [s \in Servers |-> "old"],
    load_balancer = Servers,
    remaining = Servers,
    current = 0;

fair process update_server \in Servers
begin
  Update:
    await status[self] = UPDATING;
    status[self] := "updated";
end process;

fair process coordinator = Coordinator
begin
  Loop:
    while remaining # {} do
      Remove:
        with s \in remaining do
          current := s;
          remaining := remaining \ {s};
          load_balancer := load_balancer \ {s};
        end with;
      Trigger:
        status[current] := UPDATING;
      Wait:
        await status[current] = "updated";
      Restore:
        load_balancer := load_balancer \cup {current};
    end while;
end process;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES status, load_balancer, remaining, current, pc

vars == << status, load_balancer, remaining, current, pc >>

ProcSet == (Servers) \cup {Coordinator}

Init == /\ status = [s \in Servers |-> "old"]
        /\ load_balancer = Servers
        /\ remaining = Servers
        /\ current = 0
        /\ pc = [self \in ProcSet |-> CASE self \in Servers -> "Update"
                                        [] self = Coordinator -> "Loop"]

Update(self) == /\ pc[self] = "Update"
                /\ status[self] = UPDATING
                /\ status' = [status EXCEPT ![self] = "updated"]
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << load_balancer, remaining, current >>

update_server(self) == Update(self)

Loop == /\ pc[Coordinator] = "Loop"
        /\ IF remaining # {}
              THEN /\ pc' = [pc EXCEPT ![Coordinator] = "Remove"]
              ELSE /\ pc' = [pc EXCEPT ![Coordinator] = "Done"]
        /\ UNCHANGED << status, load_balancer, remaining, current >>

Remove == /\ pc[Coordinator] = "Remove"
          /\ \E s \in remaining:
               /\ current' = s
               /\ remaining' = remaining \ {s}
               /\ load_balancer' = load_balancer \ {s}
          /\ pc' = [pc EXCEPT ![Coordinator] = "Trigger"]
          /\ UNCHANGED status

Trigger == /\ pc[Coordinator] = "Trigger"
           /\ status' = [status EXCEPT ![current] = UPDATING]
           /\ pc' = [pc EXCEPT ![Coordinator] = "Wait"]
           /\ UNCHANGED << load_balancer, remaining, current >>

Wait == /\ pc[Coordinator] = "Wait"
        /\ status[current] = "updated"
        /\ pc' = [pc EXCEPT ![Coordinator] = "Restore"]
        /\ UNCHANGED << status, load_balancer, remaining, current >>

Restore == /\ pc[Coordinator] = "Restore"
           /\ load_balancer' = load_balancer \cup {current}
           /\ pc' = [pc EXCEPT ![Coordinator] = "Loop"]
           /\ UNCHANGED << status, remaining, current >>

coordinator == Loop \/ Remove \/ Trigger \/ Wait \/ Restore

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == coordinator
           \/ (\E self \in Servers: update_server(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Servers : WF_vars(update_server(self))
        /\ WF_vars(coordinator)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")
\* END TRANSLATION

TypeOK == /\ load_balancer \subseteq Servers
          /\ remaining \subseteq Servers
          /\ \A s \in Servers : status[s] \in {"old", "updated", UPDATING}

Availability == load_balancer # {}

AllUpdated == <>(\A s \in Servers : status[s] = "updated")
=============================================================================