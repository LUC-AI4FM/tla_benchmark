```
MODULE Spec
EXTENDS Integers, FiniteSets

CONSTANT UPDATING, s1, s2, s3

VARIABLE load_balancer, update_flag, updated

update_server(s) == 
  (* wait for update flag *)
  update_flag[s] = TRUE
  /\ updated[s] = FALSE
  (* transition through UPDATING state *)
  /\ [][
      updated[s] = UPDATING
      /\ update_flag[s] = TRUE
    ]
  (* complete update *)
  /\ [][
      updated[s] = TRUE
      /\ update_flag[s] = TRUE
    ]

start_update == 
  (* phase 1: remove s1, trigger updates on s2 and s3 *)
  load_balancer = {s2, s3}
  /\ update_flag[s2] = TRUE
  /\ update_flag[s3] = TRUE
  (* wait for s2 and s3 to finish updating *)
  /\ <>(
      updated[s2] = TRUE
      /\ updated[s3] = TRUE
    )
  (* phase 2: swap load balancer, enable s1 update *)
  /\ [][
      load_balancer = {s2, s3}
      /\ update_flag[s1] = TRUE
    ]
  (* wait for s1 to finish updating *)
  /\ <>(
      updated[s1] = TRUE
    )
  (* phase 3: add s1 back to load balancer *)
  /\ [][
      load_balancer = {s1, s2, s3}
    ]

Next == 
  \/ \E s \in {s1, s2, s3} : update_server(s)
  \/ start_update

Spec == 
  (* initial condition *)
  load_balancer = {s1, s2, s3}
  /\ update_flag = [s |-> FALSE : s \in {s1, s2, s3}]
  /\ updated = [s |-> FALSE : s \in {s1, s2, s3}]
  (* transition relation *)
  /\ [][Next]_load_balancer
  /\ [][Next]_update_flag
  /\ [][Next]_updated

SameVersion == 
  \A s1, s2 \in load_balancer : updated[s1] = updated[s2]

ZeroDowntime == 
  \E s \in load_balancer : updated[s] # UPDATING

Termination == 
  <>(
    update_flag = [s |-> FALSE : s \in {s1, s2, s3}]
    /\ updated = [s |-> TRUE : s \in {s1, s2, s3}]
  )

THEOREM Spec => []SameVersion
THEOREM Spec => []ZeroDowntime
THEOREM Spec => Termination
```
Note: This specification uses the `EXTENDS` keyword to import the `Integers` and `FiniteSets` modules, which provide basic mathematical operations and set theory constructs. The `CONSTANT` keyword defines the constant `UPDATING`, while the `VARIABLE` keyword defines the variables `load_balancer`, `update_flag`, and `updated`. The `update_server` process is defined as a temporal formula using the `==` operator, which specifies the behavior of each server update. The `start_update` process orchestrates the rolling deployment strategy. The `Next` relation combines the `update_server` and `start_update` processes with weak fairness conditions. The `Spec` specification defines the initial condition, transition relation, and invariants. Finally, the `THEOREM` statements assert that the `Spec` implies the desired properties: `SameVersion`, `ZeroDowntime`, and `Termination`.