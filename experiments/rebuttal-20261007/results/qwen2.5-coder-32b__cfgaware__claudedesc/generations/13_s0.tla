------------------------------- MODULE RollingDeployment -------------------------------

CONSTANTS UPDATING

VARIABLES load_balancer, update_flag, updated

(* --algorithm rolling_deployment
variables 
    load_balancer = {"s1", "s2", "s3"},
    update_flag = <<FALSE, FALSE, FALSE>>,
    updated = <<FALSE, FALSE, FALSE>>;

process start_update \* Orchestrates the rolling deployment
begin
  while TRUE do
    await (load_balancer = {"s1", "s2", "s3"})
    load_balancer := {"s2", "s3"};
    update_flag'["s2"] := TRUE;
    update_flag'["s3"] := TRUE;

    await (\A s \in {"s2", "s3"}: updated[s] = TRUE);
    load_balancer := {"s1", "s2", "s3"};
    update_flag'["s1"] := TRUE;

    await (updated["s1"] = TRUE);
  end while;
end process

process update_server \in {"s1", "s2", "s3"} \* Updates a server
begin
  while TRUE do
    await (update_flag[self] = TRUE);
    updated'[self] := UPDATING;
    updated'[self] := TRUE;
    update_flag'[self] := FALSE;
  end while;
end process

fairness assumptions
  weak fairness start_update;
  weak fairness \A s \in {"s1", "s2", "s3"}: update_server \in {s};

invariants
  SameVersion == (\E v \in BOOLEAN \/ UPDATING: \A s \in load_balancer: updated[s] = v)
  ZeroDowntime == (\E s \in load_balancer: updated[s] # UPDATING)

liveness properties
  Termination == <>(\A s \in {"s1", "s2", "s3"}: updated[s] = TRUE)

end algorithm *)
=============================================================================