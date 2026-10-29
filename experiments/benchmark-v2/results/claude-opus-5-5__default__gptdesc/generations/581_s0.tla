---------------------------- MODULE BoundedSingleNode ----------------------------
(***************************************************************************)
(* A bounded model-checking wrapper around a single-node specification.    *)
(* The description says this module extends a separate single-node module. *)
(* That module was not provided, so its definitions are inlined in the     *)
(* "Base single-node specification" section below. This keeps the file    *)
(* self-contained and parseable by SANY.                                   *)
(*                                                                         *)
(* The constant HistoryLimit caps the number of events in the history.     *)
(* Actions that append to the history are enabled only while the history  *)
(* is shorter than HistoryLimit.                                           *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Keys,          \* set of keys stored on the node
    Values,        \* set of values that can be written
    NoValue,       \* sentinel for "no value stored"
    HistoryLimit   \* bound on the number of events in the history

ASSUME HistoryLimitAssumption == HistoryLimit \in Nat
ASSUME NoValueAssumption      == NoValue \notin Values

VARIABLES
    store,     \* store[k] is the current value of key k, or NoValue
    history    \* sequence of events observed by the node

vars == <<store, history>>

---------------------------------------------------------------------------
(***************************************************************************)
(* Base single-node specification (stands in for the imported module).    *)
(***************************************************************************)

Event ==
         [type : {"write"},  key : Keys, val : Values]
    \cup [type : {"read"},   key : Keys, val : Values \cup {NoValue}]
    \cup [type : {"delete"}, key : Keys]

TypeOK ==
    /\ store \in [Keys -> Values \cup {NoValue}]
    /\ history \in Seq(Event)

Init ==
    /\ store = [k \in Keys |-> NoValue]
    /\ history = << >>

Write(k, v) ==
    /\ store' = [store EXCEPT ![k] = v]
    /\ history' = Append(history, [type |-> "write", key |-> k, val |-> v])

Read(k) ==
    /\ history' = Append(history, [type |-> "read", key |-> k, val |-> store[k]])
    /\ UNCHANGED store

Delete(k) ==
    /\ store[k] # NoValue
    /\ store' = [store EXCEPT ![k] = NoValue]
    /\ history' = Append(history, [type |-> "delete", key |-> k])

Next ==
    \/ \E k \in Keys, v \in Values : Write(k, v)
    \/ \E k \in Keys : Read(k)
    \/ \E k \in Keys : Delete(k)

BaseSpec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(***************************************************************************)
(* Bounded wrapper                                                         *)
(***************************************************************************)

HistoryBelowLimit == Len(history) < HistoryLimit

BoundedWrite(k, v) ==
    /\ HistoryBelowLimit
    /\ Write(k, v)

BoundedRead(k) ==
    /\ HistoryBelowLimit
    /\ Read(k)

BoundedDelete(k) ==
    /\ HistoryBelowLimit
    /\ Delete(k)

BoundedNext ==
    \/ \E k \in Keys, v \in Values : BoundedWrite(k, v)
    \/ \E k \in Keys : BoundedRead(k)
    \/ \E k \in Keys : BoundedDelete(k)

Spec == Init /\ [][BoundedNext]_vars

---------------------------------------------------------------------------
(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

HistoryBounded == Len(history) <= HistoryLimit

(* Every read event returns the value of the most recent earlier write to *)
(* that key, or NoValue if there was none or a later delete occurred.     *)
LastValueBefore(k, i) ==
    LET relevant == {j \in 1..(i - 1) :
                        /\ history[j].key = k
                        /\ history[j].type \in {"write", "delete"}}
    IN  IF relevant = {}
          THEN NoValue
          ELSE LET m == CHOOSE j \in relevant : \A j2 \in relevant : j2 <= j
               IN  IF history[m].type = "write" THEN history[m].val ELSE NoValue

ReadsConsistent ==
    \A i \in 1..Len(history) :
        history[i].type = "read" =>
            history[i].val = LastValueBefore(history[i].key, i)

StoreMatchesHistory ==
    \A k \in Keys : store[k] = LastValueBefore(k, Len(history) + 1)

THEOREM Spec => [](TypeOK /\ HistoryBounded /\ ReadsConsistent /\ StoreMatchesHistory)
=============================================================================