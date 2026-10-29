--------------------------- MODULE MCSingleNode ---------------------------
(***************************************************************************)
(* Bounded model-checking wrapper around a single-node specification.     *)
(* The underlying single-node specification is included inline so that   *)
(* this module is self-contained and parses with SANY.                    *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT HistoryLimit

ASSUME HistoryLimitAssumption == HistoryLimit \in Nat

(***************************************************************************)
(*                  Underlying single-node specification                  *)
(***************************************************************************)

Keys    == {"k1", "k2"}
Values  == {"v1", "v2"}
NoValue == "none"

VARIABLES store, history, up

vars == <<store, history, up>>

Event ==
    [op : {"put", "get"}, key : Keys, val : Values \cup {NoValue}]

TypeOK ==
    /\ store \in [Keys -> Values \cup {NoValue}]
    /\ history \in Seq(Event)
    /\ up \in BOOLEAN

Init ==
    /\ store = [k \in Keys |-> NoValue]
    /\ history = <<>>
    /\ up = TRUE

\* Write a value to a key and record the event in the history.
Put(k, v) ==
    /\ up
    /\ store' = [store EXCEPT ![k] = v]
    /\ history' = Append(history, [op |-> "put", key |-> k, val |-> v])
    /\ UNCHANGED up

\* Read a key and record the observed value in the history.
Get(k) ==
    /\ up
    /\ history' = Append(history, [op |-> "get", key |-> k, val |-> store[k]])
    /\ UNCHANGED <<store, up>>

\* The node crashes; the store is durable and the history is unchanged.
Crash ==
    /\ up
    /\ up' = FALSE
    /\ UNCHANGED <<store, history>>

\* The node recovers.
Recover ==
    /\ ~up
    /\ up' = TRUE
    /\ UNCHANGED <<store, history>>

Next ==
    \/ \E k \in Keys, v \in Values : Put(k, v)
    \/ \E k \in Keys : Get(k)
    \/ Crash
    \/ Recover

(***************************************************************************)
(*                     Bounded model-checking wrapper                     *)
(***************************************************************************)

\* Bounded variants of the actions that record events in the history.
BoundedPut(k, v) ==
    /\ Len(history) < HistoryLimit
    /\ Put(k, v)

BoundedGet(k) ==
    /\ Len(history) < HistoryLimit
    /\ Get(k)

BoundedNext ==
    \/ \E k \in Keys, v \in Values : BoundedPut(k, v)
    \/ \E k \in Keys : BoundedGet(k)
    \/ Crash
    \/ Recover

BoundedSpec == Init /\ [][BoundedNext]_vars

Spec == BoundedSpec

(***************************************************************************)
(*                               Invariants                               *)
(***************************************************************************)

\* The history never grows beyond the configured limit.
HistoryBounded == Len(history) <= HistoryLimit

\* Every get observes the value of the most recent preceding put to the
\* same key (or NoValue if there was none): single-node consistency.
LastPutBefore(i, k) ==
    LET puts == {j \in 1..(i - 1) :
                    history[j].op = "put" /\ history[j].key = k}
    IN  IF puts = {} THEN NoValue
        ELSE history[CHOOSE j \in puts : \A m \in puts : m <= j].val

ReadsSeeLatestWrite ==
    \A i \in 1..Len(history) :
        history[i].op = "get" =>
            history[i].val = LastPutBefore(i, history[i].key)

=============================================================================