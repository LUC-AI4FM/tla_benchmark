------------------------------ MODULE RollingDeploy ------------------------------

EXTENDS Integers

(*
Rolling deployment for three servers behind a load balancer.
Two key safety properties are preserved by construction:
- ZeroDowntime: no server in the load balancer is mid-update, and the load balancer is never empty.
- SameVersionInLB: all servers in the load balancer always have the same version.
Termination is ensured by fairness over the coordinator actions driving the finite sequence of phases to completion.
*)

CONSTANTS

Servers == {"S1", "S2", "S3"}
Versions == {"old", "new"}
States == {"ready", "updating"}
None == "None"

VARIABLES inLB, ver, st, first, mode

vars == << inLB, ver, st, first, mode >>

Others(s) == Servers \ {s}

TypeOK ==
  /\ inLB \subseteq Servers
  /\ ver \in [Servers -> Versions]
  /\ st \in [Servers -> States]
  /\ first \in (Servers \cup {None})
  /\ mode \in {"Pick","BeginFirst","FinishFirst","Switch","BeginOthers","FinishOthers","AddOthers","Done"}

Init ==
  /\ inLB = Servers
  /\ ver = [s \in Servers |-> "old"]
  /\ st  = [s \in Servers |-> "ready"]
  /\ first = None
  /\ mode = "Pick"
  /\ TypeOK

PickFirst ==
  /\ mode = "Pick"
  /\ \E s \in inLB:
        /\ st[s] = "ready"
        /\ first' = s
        /\ inLB' = inLB \ {s}
  /\ ver' = ver
  /\ st' = st
  /\ mode' = "BeginFirst"

BeginUpdateFirst ==
  /\ mode = "BeginFirst"
  /\ first \in Servers
  /\ first \notin inLB
  /\ st[first] = "ready"
  /\ st' = [st EXCEPT ![first] = "updating"]
  /\ ver' = ver
  /\ inLB' = inLB
  /\ first' = first
  /\ mode' = "FinishFirst"

FinishUpdateFirst ==
  /\ mode = "FinishFirst"
  /\ first \in Servers
  /\ st[first] = "updating"
  /\ st' = [st EXCEPT ![first] = "ready"]
  /\ ver' = [ver EXCEPT ![first] = "new"]
  /\ inLB' = inLB
  /\ first' = first
  /\ mode' = "Switch"

SwitchToNew ==
  /\ mode = "Switch"
  /\ first \in Servers
  /\ inLB' = { first }
  /\ ver' = ver
  /\ st' = st
  /\ first' = first
  /\ mode' = "BeginOthers"

BeginUpdateOthers ==
  /\ mode = "BeginOthers"
  /\ first \in Servers
  /\ \A s \in Others(first): st[s] = "ready"
  /\ \A s \in Others(first): s \notin inLB
  /\ st' = [ s \in Servers |-> IF s \in Others(first) THEN "updating" ELSE st[s] ]
  /\ ver' = ver
  /\ inLB' = inLB
  /\ first' = first
  /\ mode' = "FinishOthers"

FinishOneOther ==
  /\ mode = "FinishOthers"
  /\ first \in Servers
  /\ \E s \in Others(first):
        /\ st[s] = "updating"
        /\ LET stNext  == [st EXCEPT ![s] = "ready"]
               verNext == [ver EXCEPT ![s] = "new"]
           IN /\ st' = stNext
              /\ ver' = verNext
              /\ inLB' = inLB
              /\ first' = first
              /\ mode' = IF \A t \in Others(first): stNext[t] = "ready"
                        THEN "AddOthers" ELSE "FinishOthers"

AddOthersToLB ==
  /\ mode = "AddOthers"
  /\ first \in Servers
  /\ \A s \in Others(first): st[s] = "ready" /\ ver[s] = "new"
  /\ inLB' = Servers
  /\ ver' = ver
  /\ st' = st
  /\ first' = first
  /\ mode' = "Done"

DoneStutter ==
  /\ mode = "Done"
  /\ UNCHANGED vars

Next ==
  PickFirst
  \/ BeginUpdateFirst
  \/ FinishUpdateFirst
  \/ SwitchToNew
  \/ BeginUpdateOthers
  \/ FinishOneOther
  \/ AddOthersToLB
  \/ DoneStutter

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(PickFirst)
  /\ WF_vars(BeginUpdateFirst)
  /\ WF_vars(FinishUpdateFirst)
  /\ WF_vars(SwitchToNew)
  /\ WF_vars(BeginUpdateOthers)
  /\ WF_vars(FinishOneOther)
  /\ WF_vars(AddOthersToLB)

(*
Safety properties (hold in all behaviors of Spec by construction)
*)
ZeroDowntime ==
  /\ inLB # {}
  /\ \A s \in inLB: st[s] = "ready"

SameVersionInLB ==
  \A s \in inLB: \A t \in inLB: ver[s] = ver[t]

AllUpdated ==
  \A s \in Servers: st[s] = "ready" /\ ver[s] = "new"

THEOREM Spec => []TypeOK /\ []ZeroDowntime /\ []SameVersionInLB /\ <>AllUpdated

=============================================================================