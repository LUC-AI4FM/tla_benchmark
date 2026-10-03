------------------------------ MODULE KeyValueStore ------------------------------
EXTENDS Naturals

CONSTANTS Keys, Vals, MISSING

VARIABLE store, op, args, retVal

TypeOK == 
  /\ store ∈ [Keys -> (Vals ∪ {MISSING})]
  /\ op ∈ {"get","insert","update","delete","idle"}
  /\ args ∈ [1 -> Keys, 2 -> Vals]
  /\ retVal ∈ Vals ∪ {MISSING}

Init == 
  /\ store = [k ∈ Keys |-> MISSING]
  /\ op = "idle"
  /\ args = [1 |-> k, 2 |-> v] /\ k ∈ Keys /\ v ∈ Vals
