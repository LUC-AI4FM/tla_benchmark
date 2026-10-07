------------------------------- MODULE RollingDeployment -------------------------------
EXTENDS TLC, FiniteSets

CONSTANTS UPDATING

VARIABLES load_balancer, update_flag, updated

Init == /\ load_balancer = {"s1", "s2", "s3"}
        /\ update_flag = <<FALSE, FALSE, FALSE>>
        /\ updated = <<FALSE, FALSE, FALSE>>

Next ==
    \/ \/ \* start_update process
       \/  /\ load_balancer = {"s1", "s2", "s3"}
           /\ update_flag' = <<TRUE, TRUE, TRUE>>
           /\ updated' = updated
           /\ load_balancer' = {"s2", "s3"}
       \/  /\ load_balancer = {"s2", "s3"}
           /\ \A i \in {1, 2, 3} : updated[i] # UPDATING
           /\ update_flag' = <<FALSE, FALSE, FALSE>>
           /\ updated' = updated
           /\ load_balancer' = {"s1", "s2", "s3"}
       \/  /\ load_balancer = {"s1", "s2", "s3"}
           /\ \A i \in {1, 2, 3} : updated[i] # UPDATING
           /\ update_flag' = <<TRUE, FALSE, FALSE>>
           /\ updated' = updated
           /\ load_balancer' = {"s2", "s3"}
       \/  /\ load_balancer = {"s2", "s3"}
           /\ \A i \in {1, 2, 3} : updated[i] # UPDATING
           /\ update_flag' = <<FALSE, FALSE, FALSE>>
           /\ updated' = updated
           /\ load_balancer' = {"s1", "s2", "s3"}
    \/ \/ \* update_server processes
       \/  /\ update_flag[1]
           /\ updated' = [updated EXCEPT ![1] = UPDATING]
           /\ load_balancer' = load_balancer
           /\ update_flag' = update_flag
       \/  /\ updated[1] = UPDATING
           /\ updated' = [updated EXCEPT ![1] = TRUE]
           /\ load_balancer' = load_balancer
           /\ update_flag' = update_flag
       \/  /\ update_flag[2]
           /\ updated' = [updated EXCEPT ![2] = UPDATING]
           /\ load_balancer' = load_balancer
           /\ update_flag' = update_flag
       \/  /\ updated[2] = UPDATING
           /\ updated' = [updated EXCEPT ![2] = TRUE]
           /\ load_balancer' = load_balancer
           /\ update_flag' = update_flag
       \/  /\ update_flag[3]
           /\ updated' = [updated EXCEPT ![3] = UPDATING]
           /\ load_balancer' = load_balancer
           /\ update_flag' = update_flag
       \/  /\ updated[3] = UPDATING
           /\ updated' = [updated EXCEPT ![3] = TRUE]
           /\ load_balancer' = load_balancer
           /\ update_flag' = update_flag

Spec ==
    /\ Init
    /\ [][Next]_<<load_balancer, update_flag, updated>>
    /\ WF_next(<<load_balancer, update_flag, updated>>)

SameVersion ==
    \A s1, s2 \in load_balancer : updated[s1] = updated[s2]

ZeroDowntime ==
    \E s \in load_balancer : updated[s] # UPDATING

Termination ==
    <>(\A i \in {1, 2, 3} : updated[i] = TRUE)

=============================================================================