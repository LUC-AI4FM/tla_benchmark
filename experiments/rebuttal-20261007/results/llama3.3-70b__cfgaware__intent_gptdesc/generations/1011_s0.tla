--------------------------- MODULE Spec ---------------------------
EXTENDS Integers, TLC

CONSTANT Keys, Values, MissingValue
VARIABLES store, requestKey, requestValue, operation, response

TypeInvariant == 
  store \in [Keys -> Values] /\ 
  requestKey \in Keys \/ requestKey = <<None>> /\ 
  requestValue \in Values \/ requestValue = <<None>> /\ 
  operation \in {"get", "insert", "update", "delete"} \/ operation = <<None>> /\ 
  response \in {"ok", "error", MissingValue} \/ response = <<None>>

Init == 
  store = [k \in Keys |-> MissingValue] /\ 
  requestKey = <<None>> /\ 
  requestValue = <<None>> /\ 
  operation = <<None>> /\ 
  response = <<None>>

GetRequest == 
  /\ operation = "get" 
  /\ requestKey \in Keys
  /\ UNCHANGED store

GetResponse == 
  /\ operation = "get"
  /\ response = IF store[requestKey] = MissingValue THEN MissingValue ELSE store[requestKey]
  /\ UNCHANGED store
  /\ requestKey = <<None>>
  /\ operation = <<None>>

InsertRequest == 
  /\ operation = "insert" 
  /\ requestKey \in Keys
  /\ requestValue \in Values

InsertResponse == 
  /\ operation = "insert"
  /\ IF store[requestKey] = MissingValue THEN 
    /\ response = "ok"
    /\ store' = [store EXCEPT ![requestKey] = requestValue]
  ELSE 
    /\ response = "error"
    /\ UNCHANGED store
  /\ requestKey = <<None>>
  /\ requestValue = <<None>>
  /\ operation = <<None>>

UpdateRequest == 
  /\ operation = "update" 
  /\ requestKey \in Keys
  /\ requestValue \in Values

UpdateResponse == 
  /\ operation = "update"
  /\ IF store[requestKey] # MissingValue THEN 
    /\ response = "ok"
    /\ store' = [store EXCEPT ![requestKey] = requestValue]
  ELSE 
    /\ response = "error"
    /\ UNCHANGED store
  /\ requestKey = <<None>>
  /\ requestValue = <<None>>
  /\ operation = <<None>>

DeleteRequest == 
  /\ operation = "delete" 
  /\ requestKey \in Keys

DeleteResponse == 
  /\ operation = "delete"
  /\ response = "ok"
  /\ store' = [store EXCEPT ![requestKey] = MissingValue]
  /\ requestKey = <<None>>
  /\ operation = <<None>>

Next == 
  \/ (operation = <<None>> /\ GetRequest)
  \/ (operation = "get" /\ GetResponse)
  \/ (operation = <<None>> /\ InsertRequest)
  \/ (operation = "insert" /\ InsertResponse)
  \/ (operation = <<None>> /\ UpdateRequest)
  \/ (operation = "update" /\ UpdateResponse)
  \/ (operation = <<None>> /\ DeleteRequest)
  \/ (operation = "delete" /\ DeleteResponse)

Spec == 
  Init /\ [][Next]_store

THEOREM Spec => []TypeInvariant
THEOREM Spec => WF_vars(Next)
=============================================================================