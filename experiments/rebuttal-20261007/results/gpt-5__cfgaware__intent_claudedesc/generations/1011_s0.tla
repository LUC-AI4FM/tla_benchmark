---- MODULE KeyValueStore ----

CONSTANTS KEYS, VALUES

(*
  Assumptions about sentinel values not being members of KEYS/VALUES.
  These can be ensured by the model configuration.
*)
ASSUME
  /\ "missing" \notin VALUES
  /\ "undef" \notin KEYS
  /\ "undef" \notin VALUES
  /\ "ok" \notin VALUES
  /\ "error" \notin VALUES

OP == {"get", "insert", "update", "delete"}
ValDom == VALUES \cup {"undef"}

VARIABLES
  store,    \* key -> (value or "missing")
  phase,    \* "Idle" | "Requested" | "Processed"
  op,       \* "none" | one of OP
  argK,     \* key argument (or "undef" when none)
  argV,     \* value argument (or "undef" when none)
  res       \* response value: value | "missing" | "ok" | "error" | "undef"

vars == << store, phase, op, argK, argV, res >>

TypeOK ==
  /\ store \in [KEYS -> (VALUES \cup {"missing"})]
  /\ phase \in {"Idle", "Requested", "Processed"}
  /\ op \in (OP \cup {"none"})
  /\ argK \in (KEYS \cup {"undef"})
  /\ argV \in (VALUES \cup {"undef"})
  /\ res \in (VALUES \cup {"missing"} \cup {"ok", "error", "undef"})

Init ==
  /\ store = [k \in KEYS |-> "missing"]
  /\ phase = "Idle"
  /\ op = "none"
  /\ argK = "undef"
  /\ argV = "undef"
  /\ res = "undef"

ValidReq(o, k, v) ==
  /\ o \in OP
  /\ k \in KEYS
  /\ IF o \in {"insert", "update"} THEN v \in VALUES ELSE v = "undef"

Request ==
  /\ phase = "Idle"
  /\ \E o \in OP, k \in KEYS, v \in ValDom:
       /\ ValidReq(o, k, v)
       /\ phase' = "Requested"
       /\ op' = o
       /\ argK' = k
       /\ argV' = v
       /\ UNCHANGED << store, res >>

GetProcess ==
  /\ phase = "Requested"
  /\ op = "get"
  /\ res' = store[argK]
  /\ phase' = "Processed"
  /\ UNCHANGED << store, op, argK, argV >>

InsertProcess ==
  /\ phase = "Requested"
  /\ op = "insert"
  /\ IF store[argK] = "missing" THEN
       /\ store' = [store EXCEPT ![argK] = argV]
       /\ res' = "ok"
     ELSE
       /\ UNCHANGED store
       /\ res' = "error"
  /\ phase' = "Processed"
  /\ UNCHANGED << op, argK, argV >>

UpdateProcess ==
  /\ phase = "Requested"
  /\ op = "update"
  /\ IF store[argK] # "missing" THEN
       /\ store' = [store EXCEPT ![argK] = argV]
       /\ res' = "ok"
     ELSE
       /\ UNCHANGED store
       /\ res' = "error"
  /\ phase' = "Processed"
  /\ UNCHANGED << op, argK, argV >>

DeleteProcess ==
  /\ phase = "Requested"
  /\ op = "delete"
  /\ store' = [store EXCEPT ![argK] = "missing"]
  /\ res' = "ok"
  /\ phase' = "Processed"
  /\ UNCHANGED << op, argK, argV >>

Process == GetProcess \/ InsertProcess \/ UpdateProcess \/ DeleteProcess

Return ==
  /\ phase = "Processed"
  /\ phase' = "Idle"
  /\ op' = "none"
  /\ argK' = "undef"
  /\ argV' = "undef"
  /\ res' = "undef"
  /\ UNCHANGED store

Next == Request \/ Process \/ Return

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(DeleteProcess)

====