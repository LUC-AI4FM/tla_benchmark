---------------------------- MODULE BoundedSingleNode ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(* Single-node base specification (inlined so the module is self-contained) *)
(***************************************************************************)

CONSTANTS Keys, Values, NoValue, HistoryLimit

ASSUME HistoryLimit \in Nat
ASSUME NoValue \notin Values

VARIABLES store, history, up

vars == <<store, history, up>>

Event == [type : {"put"}, key : Keys, val : Values]
           \cup [type : {"get"}, key : Keys, val : Values \cup {NoValue}]
           \cup [type : {"crash", "recover"}]

TypeOK ==
    /\ store \in [Keys -> Values \cup {NoValue}]
    /\ history \in Seq(Event)
    /\ up \in BOOLEAN

Init ==
    /\ store = [k \in Keys |-> NoValue]
    /\ history = << >>
    /\ up = TRUE

Put(k, v) ==
    /\ up
    /\ store' = [store EXCEPT ![k] = v]
    /\ history' = Append(history, [type |-> "put", key |-> k, val |-> v])
    /\ UNCHANGED up

Get(k) ==
    /\ up
    /\ history' = Append(history, [type |-> "get", key |-> k, val |-> store[k]])
    /\ UNCHANGED <<store, up>>

Crash ==
    /\ up
    /\ up' = FALSE
    /\ history' = Append(history, [type |-> "crash"])
    /\ UNCHANGED store

Recover ==
    /\ ~up
    /\ up' = TRUE
    /\ history' = Append(history, [type |-> "recover"])
    /\ UNCHANGED store

Next ==
    \/ \E k \in Keys, v \in Values : Put(k, v)
    \/ \E k \in Keys : Get(k)
    \/ Crash
    \/ Recover

(***************************************************************************)
(* Bounded model-checking wrapper                                           *)
(***************************************************************************)

WithinLimit == Len(history) < HistoryLimit

BoundedPut(k, v) ==
    /\ WithinLimit
    /\ Put(k, v)

BoundedGet(k) ==
    /\ WithinLimit
    /\ Get(k)

BoundedCrash ==
    /\ WithinLimit
    /\ Crash

BoundedRecover ==
    /\ WithinLimit
    /\ Recover

BoundedNext ==
    \/ \E k \in Keys, v \in Values : BoundedPut(k, v)
    \/ \E k \in Keys : BoundedGet(k)
    \/ BoundedCrash
    \/ BoundedRecover

BoundedSpec == Init /\ [][BoundedNext]_vars

Spec == BoundedSpec

(***************************************************************************)
(* Safety invariants                                                        *)
(***************************************************************************)

HistoryBounded == Len(history) <= HistoryLimit

ReadsSeeLastWrite ==
    \A i \in 1..Len(history) :
        history[i].type = "get" =>
            LET k == history[i].key
                priorPuts == {j \in 1..(i - 1) :
                                history[j].type = "put" /\ history[j].key = k}
            IN IF priorPuts = {}
                  THEN history[i].val = NoValue
                  ELSE LET m == CHOOSE j \in priorPuts :
                                    \A j2 \in priorPuts : j2 <= j
                       IN history[i].val = history[m].val

THEOREM BoundedSpec => [](TypeOK /\ HistoryBounded /\ ReadsSeeLastWrite)
=================================================================================