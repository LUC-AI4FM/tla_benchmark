------------------------------ MODULE KVStore ------------------------------
EXTENDS Naturals, TLC

CONSTANTS Keys, Vals, MISSING, NIL

(* Operation names *)
OpSet == {"get", "insert", "update", "delete"}

TupleSet == { <<k, v>> : k ∈ Keys /\ v ∈ Vals }

VARIABLES op, args, ret, dict, state

vars == <<op, args, ret, dict, state>>

Init ==
  /\ state = "ready"
  /\ op = NIL
  /\ args = NIL
  /\ ret = NIL
  /\ dict = [k ∈ Keys |->