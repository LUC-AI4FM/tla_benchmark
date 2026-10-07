MODULE RollingDeployment
EXTENDS Naturals

CONSTANTS s1, s2, s3, UPDATING

VARIABLES load_balancer, update_flag, updated

SERVERS == {s1, s2, s3}

Init ==
  /\ load_balancer = SERVERS
  /\ update_flag = [s ∈ SERVERS |-> FALSE]
  /\ updated = [s ∈ SERVERS |-> FALSE]

Phase1 ==
  /\ s1 ∈ load_balancer
  /\ update_flag[s2] = FALSE
  /\ update_flag[s3] = FALSE
  /\ load_balancer' = load_balancer \ {s1}
  /\ update_flag' = [update_flag EXCEPT ![s2] = TRUE, ![s3] = TRUE]
  /\ updated' = updated

Phase2 ==
  /\ s1 ∉ load_balancer
  /\ updated[s2] = TRUE
  /\ updated[s3] = TRUE
  /\ update_flag[s1] = FALSE
  /\ load_balancer' = {s2, s3}
  /\ update_flag' = [update_flag EXCEPT ![s1] = TRUE]
  /\ updated' = updated

Phase3 ==
  /\ s1 ∉ load_balancer
  /\ updated[s1] = TRUE
  /\ load_balancer' = load_balancer ∪ {s1}
  /\ update_flag' = [update_flag EXCEPT ![s1] = FALSE]
  /\ updated' = updated

UpdateStep1(s) ==
  /\ s ∈ SERVERS
  /\ update_flag[s] = TRUE
  /\ updated[s] = FALSE
  /\ load_balancer' = load_balancer
  /\ update_flag' = update_flag
  /\ updated' = [updated EXCEPT ![s] = UPDATING]

UpdateStep2(s) ==
  /\ s ∈ SERVERS
  /\ update_flag[s] = TRUE
  /\ updated[s] = UPDATING
  /\ load_balancer' = load_balancer
  /\ update_flag' = update_flag
  /\ updated' = [updated EXCEPT ![s] = TRUE]

Next ==
  Phase1 \/ Phase2 \/ Phase3
  \/ ∨ s ∈ SERVERS : UpdateStep1(s)
  \/ ∨ s ∈ SERVERS : UpdateStep2(s)

SameVersion ==
  ∀ s1 ∈ load_balancer ∀ s2 ∈ load_balancer :
    updated[s1] = updated[s2]

ZeroDowntime ==
  ∃ s ∈ load_balancer : updated[s] # UPDATING

Termination ==
  ∧ ∀ s ∈ SERVERS : <> (updated[s] = TRUE)

Spec ==
  Init
  /\ [][Next]_vars
  /\ WF_vars(Phase1 \/ Phase2 \/ Phase3)
  /\ ∧ ∀ s ∈ SERVERS : WF_vars(UpdateStep1(s) \/ UpdateStep2(s))

Safety == SameVersion /\ ZeroDowntime

Liveness == Termination

===============================================================================