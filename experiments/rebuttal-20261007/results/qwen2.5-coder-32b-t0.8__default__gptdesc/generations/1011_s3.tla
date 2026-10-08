------------------------------- MODULE KeyValueStore --------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Keys, Vals
VARIABLES store, currentOp, keyArg, valArg, retValue, ready

Init == 
  /\ store = [k \in Keys |-> "MISSING"]
  /\ currentOp = "idle"
  /\ keyArg \notin Keys
  /\ valArg \notin Vals
  /\ retValue \notin Vals \/ retValue = "MISSING"
  /\ ready = TRUE

TypeOK ==
  /\ store \in [Keys -> Vals \/ {"MISSING"}]
  /\ currentOp \in {"idle", "get", "insert", "update", "delete"}
  /\ keyArg \in Keys \/ keyArg \notin Keys
  /\ valArg \in Vals \/ valArg \notin Vals
  /\ retValue \in Vals \/ retValue = "MISSING"
  /\ ready \in {TRUE, FALSE}

Get ==
  /\ currentOp = "get"
  /\ keyArg \in Keys
  /\ ready
  /\ retValue' = store[keyArg]
  /\ currentOp' = "idle"
  /\ keyArg' \notin Keys
  /\ valArg' \notin Vals
  /\ ready' = TRUE

Insert ==
  /\ currentOp = "insert"
  /\ keyArg \in Keys
  /\ valArg \in Vals
  /\ ready
  /\ store' = [store EXCEPT ![keyArg] = valArg]
  /\ retValue' = "SUCCESS"
  /\ currentOp' = "idle"
  /\ keyArg' \notin Keys
  /\ valArg' \notin Vals
  /\ ready' = TRUE

Update ==
  /\ currentOp = "update"
  /\ keyArg \in Keys
  /\ valArg \in Vals
  /\ store[keyArg] \in Vals
  /\ ready
  /\ store' = [store EXCEPT ![keyArg] = valArg]
  /\ retValue' = "SUCCESS"
  /\ currentOp' = "idle"
  /\ keyArg' \notin Keys
  /\ valArg' \notin Vals
  /\ ready' = TRUE

Delete ==
  /\ currentOp = "delete"
  /\ keyArg \in Keys
  /\ store[keyArg] \in Vals
  /\ ready
  /\ store' = [store EXCEPT ![keyArg] = "MISSING"]
  /\ retValue' = "SUCCESS"
  /\ currentOp' = "idle"
  /\ keyArg' \notin Keys
  /\ valArg' \notin Vals
  /\ ready' = TRUE

Next ==
  \/ Get
  \/ Insert
  \/ Update
  \/ Delete
  \/ /\ ready
     /\ currentOp' = "idle"
     /\ retValue' = "NOOP"
     /\ keyArg' \notin Keys
     /\ valArg' \notin Vals
     /\ ready' = TRUE

Spec ==
  /\ Init
  /\ [][Next]_<<store, currentOp, keyArg, valArg, retValue, ready>>
  /\ WF_next_op(delete)

=============================================================================