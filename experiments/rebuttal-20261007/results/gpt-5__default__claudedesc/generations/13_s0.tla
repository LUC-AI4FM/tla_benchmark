----------------------------- MODULE RollingDeployment -----------------------------

EXTENDS Naturals

CONSTANT UPDATING
ASSUME UPDATING ∉ BOOLEAN

(*
  Fixed set of servers
*)
SERVERS == {"s1", "s2", "s3"}

VARIABLES
  load_balancer,
  update_flag,    \* [s ∈ SERVERS -> BOOLEAN]
  updated,        \* [s ∈ SERVERS -> {FALSE, UPDATING, TRUE}]
  suPhase         \* 0,1,2,3 phases for start_update orchestrator

vars == << load_balancer, update_flag, updated, suPhase >>

Init ==
  /\ load_balancer = SERVERS
  /\ update_flag = [s \in SERVERS |-> FALSE]
  /\ updated = [s \in SERVERS |-> FALSE]
  /\ suPhase = 0

(*
  Orchestration (start_update) in three phases:
  - Phase0: remove "s1" from LB, trigger updates on "s2","s3"
  - Phase1: once "s2","s3" finished, switch LB to {"s2","s3"} and enable "s1"
  - Phase2: once "s1" finished, add it back to LB (all three)
*)
Phase0 ==
  /\ suPhase = 0
  /\ load_balancer' = SERVERS \ {"s1"}
  /\ update_flag' = [update_flag EXCEPT !["s2"] = TRUE, !["s3"] = TRUE]
  /\ updated' = updated
  /\ suPhase' = 1

Phase1 ==
  /\ suPhase = 1
  /\ updated["s2"] = TRUE
  /\ updated["s3"] = TRUE
  /\ load_balancer' = {"s2", "s3"}
  /\ update_flag' = [update_flag EXCEPT !["s1"] = TRUE]
  /\ updated' = updated
  /\ suPhase' = 2

Phase2 ==
  /\ suPhase = 2
  /\ updated["s1"] = TRUE
  /\ load_balancer' = SERVERS
  /\ UNCHANGED << update_flag, updated >>
  /\ suPhase' = 3

StartAction == Phase0 \/ Phase1 \/ Phase2

(*
  Per-server update_server process:
  - Wait for flag
  - FALSE -> UPDATING
  - UPDATING -> TRUE
*)
UpdateStart(s) ==
  /\ s \in SERVERS
  /\ update_flag[s] = TRUE
  /\ updated[s] = FALSE
  /\ updated' = [updated EXCEPT ![s] = UPDATING]
  /\ UNCHANGED << load_balancer, update_flag, suPhase >>

UpdateFinish(s) ==
  /\ s \in SERVERS
  /\ updated[s] = UPDATING
  /\ updated' = [updated EXCEPT ![s] = TRUE]
  /\ UNCHANGED << load_balancer, update_flag, suPhase >>

UpdateAction ==
  \E s \in SERVERS: UpdateStart(s) \/ UpdateFinish(s)

Stutter == UNCHANGED vars

Next == StartAction \/ UpdateAction \/ Stutter

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(StartAction)
  /\ \A s \in SERVERS: WF_vars(UpdateStart(s)) /\ WF_vars(UpdateFinish(s))

(*
  Safety invariants
*)
TypeOK ==
  /\ load_balancer \subseteq SERVERS
  /\ update_flag \in [SERVERS -> BOOLEAN]
  /\ updated \in [SERVERS -> {FALSE, UPDATING, TRUE}]
  /\ suPhase \in 0..3

SameVersion ==
  \A s, t \in load_balancer: updated[s] = updated[t]

ZeroDowntime ==
  load_balancer = {} \/ (\E s \in load_balancer: updated[s] # UPDATING)

Safety == TypeOK /\ SameVersion /\ ZeroDowntime

(*
  Liveness: all processes eventually finish (termination)
*)
Termination ==
  <> (/\ suPhase = 3
      /\ \A s \in SERVERS: updated[s] = TRUE
      /\ load_balancer = SERVERS)

=============================================================================