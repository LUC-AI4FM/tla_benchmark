---- MODULE RollingDeploy ----
EXTENDS TLC, Sequences, Integers, FiniteSets

CONSTANT UPDATING

Servers == {"s1", "s2", "s3"}

VARIABLES load_balancer, update_flag, updated, pc

vars == << load_balancer, update_flag, updated, pc >>

ProcSet == {"start_update"} \cup Servers

Init ==
    /\ load_balancer = Servers
    /\ update_flag = [s \in Servers |-> FALSE]
    /\ updated = [s \in Servers |-> FALSE]
    /\ pc = [self \in ProcSet |-> CASE self = "start_update" -> "Start"
                                    [] self \in Servers -> "Update"]

\* start_update process

Start ==
    /\ pc["start_update"] = "Start"
    /\ load_balancer' = Servers \ {"s1"}
    /\ update_flag' = [update_flag EXCEPT !["s2"] = TRUE, !["s3"] = TRUE]
    /\ pc' = [pc EXCEPT !["start_update"] = "Transition"]
    /\ UNCHANGED updated

Transition ==
    /\ pc["start_update"] = "Transition"
    /\ updated["s2"] = TRUE
    /\ updated["s3"] = TRUE
    /\ load_balancer' = {"s2", "s3"}
    /\ update_flag' = [update_flag EXCEPT !["s1"] = TRUE]
    /\ pc' = [pc EXCEPT !["start_update"] = "Finish"]
    /\ UNCHANGED updated

FinishStart ==
    /\ pc["start_update"] = "Finish"
    /\ updated["s1"] = TRUE
    /\ load_balancer' = load_balancer \cup {"s1"}
    /\ pc' = [pc EXCEPT !["start_update"] = "Done"]
    /\ UNCHANGED << update_flag, updated >>

start_update == Start \/ Transition \/ FinishStart

\* update_server processes

Update(self) ==
    /\ pc[self] = "Update"
    /\ update_flag[self]
    /\ updated' = [updated EXCEPT ![self] = UPDATING]
    /\ pc' = [pc EXCEPT ![self] = "FinishUpdate"]
    /\ UNCHANGED << load_balancer, update_flag >>

FinishUpdate(self) ==
    /\ pc[self] = "FinishUpdate"
    /\ updated' = [updated EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED << load_balancer, update_flag >>

update_server(self) == Update(self) \/ FinishUpdate(self)

Terminating ==
    /\ \A self \in ProcSet : pc[self] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ start_update
    \/ (\E self \in Servers : update_server(self))
    \/ Terminating

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(start_update)
    /\ \A self \in Servers : WF_vars(update_server(self))

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

\* Invariants

SameVersion ==
    \A s1, s2 \in load_balancer : updated[s1] = updated[s2]

ZeroDowntime ==
    \E s \in load_balancer : updated[s] # UPDATING

====