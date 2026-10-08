```tla
---- MODULE MutualExclusionLock ----
EXTENDS TLC, Integers

CONSTANTS P \* Set of processes {1, 2}

VARIABLES loc, lock

Init == /\ loc = [p \in P -> "non-critical"]
        /\ lock = FALSE

Next ==
    \/ /\ loc[1] = "non-critical"
       /\ loc' = [loc EXCEPT ![1] = "waiting"]
       /\ UNCHANGED <<lock>>
    \/ /\ loc[1] = "waiting"
       /\ \A p \in P \ {1} : loc[p] # "critical"
       /\ lock
       /\ loc' = [loc EXCEPT ![1] = "waiting"]
       /\ UNCHANGED <<lock>>
    \/ /\ loc[1] = "waiting"
       /\ \A p \in P \ {1} : loc[p] # "critical"
       /\ ~lock
       /\ loc' = [loc EXCEPT ![1] = "critical"]
       /\ lock'
    \/ /\ loc[1] = "critical"
       /\ loc' = [loc EXCEPT ![1] = "non-critical"]
       /\ lock'
    \/ /\ loc[2] = "non-critical"
       /\ loc' = [loc EXCEPT ![2] = "waiting"]
       /\ UNCHANGED <<lock>>
    \/ /\ loc[2] = "waiting"
       /\ \A p \in P \ {2} : loc[p] # "critical"
       /\ lock
       /\ loc' = [loc EXCEPT ![2] = "waiting"]
       /\ UNCHANGED <<lock>>
    \/ /\ loc[2] = "waiting"
       /\ \A p \in P \ {2} : loc[p] # "critical"
       /\ ~lock
       /\ loc' = [loc EXCEPT ![2] = "critical"]
       /\ lock'
    \/ /\ loc[2] = "critical"
       /\ loc' = [loc EXCEPT ![2] = "non-critical"]
       /\ lock'

MutualExclusion == \A p1, p2 \in P : p1 # p2 => ~ (loc[p1] = "critical" /\ loc[p2] = "critical")

Spec ==
    /\ Init
    /\ [][Next]_<<loc, lock>>
    /\ <>[<>](MutualExclusion)
    /\ WF_[<>(loc[1] = "waiting")](loc[1] = "critical")
```
```