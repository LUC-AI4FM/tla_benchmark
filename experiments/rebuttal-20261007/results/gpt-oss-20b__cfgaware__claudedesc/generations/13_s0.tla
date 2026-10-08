------------------------------ MODULE RollingDeployment ------------------------------
EXTENDS Naturals, TLC

CONSTANTS SERVERS, UPDATING

VARIABLES load_balancer, update_flag, updated

(* --------------------------------------------------------------------------- *)
(* Initial state *)
Init ==
  /\ load_balancer = SERVERS
  /\ update_flag = [s \in SERVERS |-> FALSE]
  /\ updated     = [s \in SERVERS |-> FALSE]

(* --------------------------------------------------------------------------- *)
(* Actions orchestrating the rolling deployment *)

Phase1 ==
  /\ load_balancer = SERVERS
  /\ ~update_flag["s1"]
  /\ ~update_flag["s2"]
  /\ ~update_flag["s3"]
  /\ update_flag' = [update_flag EXCEPT !["s2"] = TRUE, !["s3"] = TRUE]
  /\ load_balancer' = SERVERS \ {"s1"}
  /\ updated'      = updated

Phase2 ==
  /\ updated["s2"] = TRUE
  /\ updated["s3"] = TRUE
  /\ ~update_flag["s1"]
  /\ update_flag' = [update_flag EXCEPT !["s1"] = TRUE]
  /\ load_balancer' = load_balancer
  /\ updated'      = updated

Phase3 ==
  /\ updated["s1"] = TRUE
  /\ load_balancer' = SERVERS
  /\ update_flag'   = update_flag
  /\ updated'       = updated

start_update == Phase1 \/ Phase2 \/ Phase3

(* --------------------------------------------------------------------------- *)
(* Per‑server update actions *)

UpdateStart(s) ==
  /\ s \in SERVERS
  /\ update_flag[s]
  /\ updated[s] = FALSE
  /\ updated'     = [updated EXCEPT ![s] = UPDATING]
  /\ load_balancer'= load_balancer
  /\ update_flag'   = update_flag

UpdateFinish(s) ==
  /\ s \in SERVERS
  /\ updated[s] = UPDATING
  /\ updated'     = [updated EXCEPT ![s] = TRUE]
  /\ update_flag' = [update_flag EXCEPT ![s] = FALSE]
  /\ load_balancer'= load_balancer

UpdateServer ==
  \/ \E s \in SERVERS : UpdateStart(s)
  \/ \E s \in SERVERS : UpdateFinish(s)

(* --------------------------------------------------------------------------- *)
(* Next action *)

Next == start_update \/ UpdateServer

(* --------------------------------------------------------------------------- *)
(* Invariants *)

SameVersion ==
  \A s1, s2 \in load_balancer :
    updated[s1] = updated[s2]

ZeroDowntime ==
  \E s \in load_balancer :
    updated[s] ~= UPDATING

(* --------------------------------------------------------------------------- *)
(* Liveness property *)

Termination == WF_action(start_update) /\ WF_action(UpdateServer)

(* --------------------------------------------------------------------------- *)
(* The complete specification *)

Spec == Init
        /\ [][Next]_<<load_balancer, update_flag, updated>>
        /\ Termination
=============================================================================