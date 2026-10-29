---------------------------- MODULE RollingDeploy ----------------------------
EXTENDS TLC, FiniteSets

CONSTANT UPDATING

Servers == {"s1", "s2", "s3"}

ASSUME UPDATING \notin BOOLEAN

VARIABLES load_balancer, update_flag, updated, pc

vars == << load_balancer, update_flag, updated, pc >>

Orchestrator == "orchestrator"

ProcSet == {Orchestrator} \cup Servers

(* --------------------------- Invariants --------------------------- *)

SameVersion ==
    \A x, y \in load_balancer : updated[x] = updated[y]

ZeroDowntime ==
    \E s \in load_balancer : updated[s] # UPDATING

TypeOK ==
    /\ load_balancer \subseteq Servers
    /\ update_flag \in [Servers -> BOOLEAN]
    /\ updated \in [Servers -> {FALSE, UPDATING, TRUE}]
    /\ pc \in [ProcSet -> {"Start", "Transition", "Finish",
                            "Update", "FinishUpdate", "Done"}]

(* ------------------------------ Init ------------------------------ *)

Init ==
    /\ load_balancer = Servers
    /\ update_flag = [s \in Servers |-> FALSE]
    /\ updated = [s \in Servers |-> FALSE]
    /\ pc = [self \in ProcSet |->
                IF self = Orchestrator THEN "Start" ELSE "Update"]

(* --------------------- start_update process ---------------------- *)

Start ==
    /\ pc[Orchestrator] = "Start"
    /\ load_balancer' = {"s1"}
    /\ update_flag' = [update_flag EXCEPT !["s2"] = TRUE, !["s3"] = TRUE]
    /\ pc' = [pc EXCEPT ![Orchestrator] = "Transition"]
    /\ UNCHANGED updated

Transition ==
    /\ pc[Orchestrator] = "Transition"
    /\ updated["s2"] = TRUE /\ updated["s3"] = TRUE
    /\ load_balancer' = {"s2", "s3"}
    /\ update_flag' = [update_flag EXCEPT !["s1"] = TRUE]
    /\ pc' = [pc EXCEPT ![Orchestrator] = "Finish"]
    /\ UNCHANGED updated

Finish ==
    /\ pc[Orchestrator] = "Finish"
    /\ updated["s1"] = TRUE
    /\ load_balancer' = load_balancer \cup {"s1"}
    /\ pc' = [pc EXCEPT ![Orchestrator] = "Done"]
    /\ UNCHANGED << update_flag, updated >>

start_update == Start \/ Transition \/ Finish

(* --------------------- update_server process --------------------- *)

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

(* ------------------------------ Next ------------------------------ *)

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

(* ---------------------------- Liveness ---------------------------- *)

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

=============================================================================