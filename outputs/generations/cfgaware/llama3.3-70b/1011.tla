---------------------------- MODULE KeyValueStore ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Keys, Vals
VARIABLES store, op, key, val, ret, ready

TypeCorrect == 
  store \in [Keys -> Vals \cup {MISSING}] /\ 
  op \in {"get", "insert", "update", "delete"} /\ 
  key \in Keys /\ 
  val \in Vals /\ 
  ret \in Vals \cup {MISSING} /\ 
  ready \in BOOLEAN

Init == 
  store = [k \in Keys |-> MISSING] /\ 
  op = "get" /\ 
  key = <<>> /\ 
  val = <<>> /\ 
  ret = MISSING /\ 
  ready = TRUE

GetRequest == 
  op = "get" /\ 
  ready' = FALSE /\ 
  store' = store /\ 
  op' = "get" /\ 
  key' \in Keys /\ 
  val' = <<>> /\ 
  ret' = MISSING /\ 
  ready' = FALSE

GetResponse == 
  op = "get" /\ 
  ~ready /\ 
  ready' = TRUE /\ 
  store' = store /\ 
  op' = "get" /\ 
  key' = key /\ 
  val' = <<>> /\ 
  ret' = IF store[key] = MISSING THEN MISSING ELSE store[key] /\ 
  ready' = TRUE

InsertRequest == 
  op = "insert" /\ 
  ready' = FALSE /\ 
  store' = store /\ 
  op' = "insert" /\ 
  key' \in Keys /\ 
  val' \in Vals /\ 
  ret' = MISSING /\ 
  ready' = FALSE

InsertResponse == 
  op = "insert" /\ 
  ~ready /\ 
  ready' = TRUE /\ 
  store' = [store EXCEPT ![key] = val] /\ 
  op' = "insert" /\ 
  key' = key /\ 
  val' = val /\ 
  ret' = val /\ 
  ready' = TRUE

UpdateRequest == 
  op = "update" /\ 
  ready' = FALSE /\ 
  store' = store /\ 
  op' = "update" /\ 
  key' \in Keys /\ 
  val' \in Vals /\ 
  ret' = MISSING /\ 
  ready' = FALSE

UpdateResponse == 
  op = "update" /\ 
  ~ready /\ 
  ready' = TRUE /\ 
  store' = IF store[key] = MISSING THEN store ELSE [store EXCEPT ![key] = val] /\ 
  op' = "update" /\ 
  key' = key /\ 
  val' = val /\ 
  ret' = IF store[key] = MISSING THEN MISSING ELSE val /\ 
  ready' = TRUE

DeleteRequest == 
  op = "delete" /\ 
  ready' = FALSE /\ 
  store' = store /\ 
  op' = "delete" /\ 
  key' \in Keys /\ 
  val' = <<>> /\ 
  ret' = MISSING /\ 
  ready' = FALSE

DeleteResponse == 
  op = "delete" /\ 
  ~ready /\ 
  ready' = TRUE /\ 
  store' = [store EXCEPT ![key] = MISSING] /\ 
  op' = "delete" /\ 
  key' = key /\ 
  val' = <<>> /\ 
  ret' = MISSING /\ 
  ready' = TRUE

Next == 
  \/ GetRequest /\ GetResponse /\ 
  \/ InsertRequest /\ InsertResponse /\ 
  \/ UpdateRequest /\ UpdateResponse /\ 
  \/ DeleteRequest /\ DeleteResponse 

Spec == 
  Init /\ [][Next]_<<store, op, key, val, ret, ready>> /\ WF_(op="delete")(DeleteRequest)
=============================================================================