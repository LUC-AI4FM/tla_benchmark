```tla
MODULE RollingDeployment

EXTENDS Integers, FiniteSets

CONSTANTS UPDATING, s1, s2, s3

VARIABLES load_balancer,
          update_flag,
          updated

Init ==
  /\ load_balancer = {s1, s2, s3}
  /\ update_flag = [s1 |-> FALSE, s2 |-> FALSE, s3 |-> FALSE]
  /\ updated = [s1 |-> FALSE, s2 |-> FALSE, s3 |-> FALSE]

start_update ==
  IF update_flag[s1] = FALSE
  THEN
    /\ load_balancer' = {s2, s3}
    /\ update_flag' = [update_flag EXCEPT ![s2] = TRUE, ![s3] = TRUE]
    /\ updated' = updated
  ELSE IF update_flag[s1] = TRUE /\ updated[s1] = UPDATING
  THEN
    /\ load_balancer' = load_balancer
    /\ update_flag' = update_flag
    /\ updated' = [updated EXCEPT ![s1] = TRUE]
  ELSE
    /\ load_balancer' = {s1, s2, s3}
    /\ update_flag' = update_flag
    /\ updated' = updated

update_server(s) ==
  IF update_flag[s] = TRUE /\ updated[s] = FALSE
  THEN
    /\ load_balancer' = load_balancer
    /\ update_flag' = update_flag
    /\ updated' = [updated EXCEPT ![s] = UPDATING]
  ELSE IF update_flag[s] = TRUE /\ updated[s] = UPDATING
  THEN
    /\ load_balancer' = load_balancer
    /\ update_flag' = update_flag
    /\ updated' = [updated EXCEPT ![s] = TRUE]
  ELSE
    /\ load_balancer' = load_balancer
    /\ update_flag' = update_flag
    /\ updated' = updated

Next ==
  \/ start_update
  \/ update_server(s1)
  \/ update_server(s2)
  \/ update_server(s3)

Spec ==
  Init /\ [][Next]_<<load_balancer, update_flag, updated>>
  /\ WF_vars(start_update, <<load_balancer, update_flag, updated>>)
  /\ WF_vars(update_server(s1), <<load_balancer, update_flag, updated>>)
  /\ WF_vars(update_server(s2), <<load_balancer, update_flag, updated>>)
  /\ WF_vars(update_server(s3), <<load_balancer, update_flag, updated>>)

SameVersion ==
  \A s1, s2 \in load_balancer : updated[s1] = updated[s2]

ZeroDowntime ==
  \E s \in load_balancer : updated[s] # UPDATING

Termination ==
  <>[](update_flag[s1] = FALSE /\ update_flag[s2] = FALSE /\ update_flag[s3] = FALSE
       /\ updated[s1] = TRUE /\ updated[s2] = TRUE /\ updated[s3] = TRUE)
```