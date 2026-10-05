---------------------------- MODULE RollingDeployment ----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT UPDATING

VARIABLES load_balancer, update_flag, updated, pc

vars == <<load_balancer, update_flag, updated, pc>>

Servers == {"s1", "s2", "s3"}

Init ==
    /\ load_balancer = Servers
    /\ update_flag = [s \in Servers |-> FALSE]
    /\ updated = [s \in Servers |-> FALSE]
    /\ pc = [p \in {"start_update"} \cup Servers |-> 
                IF p = "start_update" THEN "phase1" ELSE "wait_flag"]

(* start_update process *)
phase1 ==
    /\ pc["start_update"] = "phase1"
    /\ load_balancer' = load_balancer \ {"s1"}
    /\ update_flag' = [update_flag EXCEPT !["s2"] = TRUE, !["s3"] = TRUE]
    /\ updated' = updated
    /\ pc' = [pc EXCEPT !["start_update"] = "phase2"]

phase2 ==
    /\ pc["start_update"] = "phase2"
    /\ updated["s2"] = TRUE
    /\ updated["s3"] = TRUE
    /\ load_balancer' = {"s2", "s3"}
    /\ update_flag' = [update_flag EXCEPT !["s1"] = TRUE]
    /\ updated' = updated
    /\ pc' = [pc EXCEPT !["start_update"] = "phase3"]

phase3 ==
    /\ pc["start_update"] = "phase3"
    /\ updated["s1"] = TRUE
    /\ load_balancer' = load_balancer \cup {"s1"}
    /\ update_flag' = update_flag
    /\ updated' = updated
    /\ pc' = [pc EXCEPT !["start_update"] = "done"]

start_update ==
    \/ phase1
    \/ phase2
    \/ phase3

(* update_server process for each server *)
wait_flag(s) ==
    /\ pc[s] = "wait_flag"
    /\ update_flag[s] = TRUE
    /\ updated' = [updated EXCEPT ![s] = UPDATING]
    /\ pc' = [pc EXCEPT ![s] = "updating"]
    /\ load_balancer' = load_balancer
    /\ update_flag' = update_flag

finish_update(s) ==
    /\ pc[s] = "updating"
    /\ updated[s] = UPDATING
    /\ updated' = [updated EXCEPT ![s] = TRUE]
    /\ pc' = [pc EXCEPT ![s] = "done"]
    /\ load_balancer' = load_balancer
    /\ update_flag' = update_flag

update_server(s) ==
    \/ wait_flag(s)
    \/ finish_update(s)

Next ==
    \/ start_update
    \/ \E s \in Servers : update_server(s)

Fairness ==
    /\ WF_vars(start_update)
    /\ \A s \in Servers : WF_vars(update_server(s))

Spec == Init /\ [][Next]_vars /\ Fairness

(* Invariants *)
SameVersion ==
    \A s1_server, s2_server \in load_balancer :
        updated[s1_server] = updated[s2_server]

ZeroDowntime ==
    \E s \in load_balancer : updated[s] # UPDATING

(* Liveness property *)
Termination ==
    <>(pc["start_update"] = "done" /\ \A s \in Servers : pc[s] = "done")

=============================================================================