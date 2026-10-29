------------------------------- MODULE MCSingleNode -------------------------------
(***************************************************************************)
(* Bounded model-checking wrapper around a single-node specification.     *)
(* The base single-node specification is a key-value store that records   *)
(* every client-visible operation in a history. Here it is inlined so     *)
(* that the module is self-contained. The wrapper adds the constant       *)
(* HistoryLimit, which caps the number of events recorded in the history *)
(* by guarding the history-extending actions.                             *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Keys,           \* set of keys
    Values,         \* set of values
    NoValue,        \* sentinel for an absent value
    HistoryLimit    \* bound on the length of the history

ASSUME HistoryLimit \in Nat
ASSUME NoValue \notin Values

VARIABLES
    store,      \* current key-value mapping of the single node
    history     \* sequence of recorded events

vars == <<store, history>>

---------------------------------------------------------------------------
(***************************************************************************)
(* Base single-node specification                                         *)
(***************************************************************************)

Event ==
    [type : {"write"}, key : Keys, val : Values]
  \cup [type : {"read"}, key : Keys, val : Values \cup {NoValue}]
  \cup [type : {"delete"}, key : Keys]

TypeOK ==
    /\ store \in [Keys -> Values \cup {NoValue}]
    /\ history \in Seq(Event)

Init ==
    /\ store = [k \in Keys |-> NoValue]
    /\ history = <<>>

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

SingleNodeSpec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(***************************************************************************)
(* Bounded variants of the history-extending actions                     *)
(***************************************************************************)

HistoryNotFull == Len(history) < HistoryLimit

BoundedWrite(k, v) ==
    /\ HistoryNotFull
    /\ Write(k, v)

BoundedRead(k) ==
    /\ HistoryNotFull
    /\ Read(k)

BoundedDelete(k) ==
    /\ HistoryNotFull
    /\ Delete(k)

BoundedNext ==
    \/ \E k \in Keys, v \in Values : BoundedWrite(k, v)
    \/ \E k \in Keys : BoundedRead(k)
    \/ \E k \in Keys : BoundedDelete(k)

Spec == Init /\ [][BoundedNext]_vars

---------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                      *)
(***************************************************************************)

HistoryBounded == Len(history) <= HistoryLimit

\* Every recorded read returns the value of the most recent preceding
\* write/delete to the same key (NoValue if none).
LastValueBefore(i, k) ==
    LET relevant == {j \in 1..(i - 1) :
                        /\ history[j].key = k
                        /\ history[j].type \in {"write", "delete"}}
    IN IF relevant = {} THEN NoValue
       ELSE LET m == CHOOSE j \in relevant : \A j2 \in relevant : j2 <= j
            IN IF history[m].type = "write" THEN history[m].val ELSE NoValue

ReadsLinearizable ==
    \A i \in 1..Len(history) :
        history[i].type = "read" =>
            history[i].val = LastValueBefore(i, history[i].key)

StoreMatchesHistory ==
    \A k \in Keys : store[k] = LastValueBefore(Len(history) + 1, k)

THEOREM Spec => [](TypeOK /\ HistoryBounded /\ ReadsLinearizable /\ StoreMatchesHistory)

=============================================================================