------------------------------- MODULE KeyValueStore -------------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS 
    Clients, Keys, PrimaryMap \* Clients = {C1, C2}, Keys = {K1, K2}

VARIABLES 
    store, clientState, replicaState, messages, committedTransactions

Init == 
    /\ store = [k \in Keys |-> 0]
    /\ clientState = [c \in Clients |-> <<>>] \* Each client's transaction log
    /\ replicaState = [k \in Keys |-> {seq}] \* Each key's log of committed transactions
    /\ messages = {}
    /\ committedTransactions = {}

Next == 
    \/ \E c \in Clients, rs \subseteq Keys, ws \subseteq Keys : OptimisticTransaction(c, rs, ws)
    \/ \E c \in Clients, rs \subseteq Keys, ws \subseteq Keys : PessimisticTransaction(c, rs, ws)
    \/ MessageHandling

OptimisticTransaction(c, rs, ws) ==
    /\ clientState' = [clientState EXCEPT ![c] = Append(clientState[c], <<rs, ws, "optimistic", FALSE>>)]
    /\ UNCHANGED <<store, replicaState, messages, committedTransactions>>

PessimisticTransaction(c, rs, ws) ==
    /\ clientState' = [clientState EXCEPT ![c] = Append(clientState[c], <<rs, ws, "pessimistic", FALSE>>)]
    /\ \A k \in ws : replicaState' = [replicaState EXCEPT ![PrimaryMap[k]] = replicaState[PrimaryMap[k]] \cup {"lock"}]
    /\ UNCHANGED <<store, messages, committedTransactions>>

MessageHandling ==
    \/ \E m \in messages, c \in Clients, rs \subseteq Keys, ws \subseteq Keys, style \in {"optimistic", "pessimistic"}, success \in BOOLEAN :
        /\ clientState' = [clientState EXCEPT ![c] = Append(clientState[c], <<rs, ws, style, success>>)]
        /\ messages' = messages \ {m}
        /\ UNCHANGED <<store, replicaState, committedTransactions>>
    \/ \E m \in messages, k \in Keys, t \in Seq(ANY) :
        /\ replicaState' = [replicaState EXCEPT ![PrimaryMap[k]] = replicaState[PrimaryMap[k]] \cup {t}]
        /\ store' = [store EXCEPT ![k] = Last(t)]
        /\ committedTransactions' = committedTransactions \cup {t}
        /\ messages' = messages \ {m}
        /\ UNCHANGED clientState

Spec == 
    Init /\ [][Next]_<<clientState, replicaState, messages, store, committedTransactions>>

Serializability ==
    \A t1, t2 \in committedTransactions : 
        \/ t1 = t2
        \/ \E i, j \in 1..Len(t1) : i # j /\ (t1[i] \notin t2 OR t2[j] \notin t1)

NoLostUpdates ==
    \A k \in Keys, v1, v2 \in store :
        \/ v1 = v2
        \/ \E t \in committedTransactions : Last(t) = <<k, v2>>

ReadYourWrites ==
    \A c \in Clients, rs \subseteq Keys, ws \subseteq Keys, i \in 1..Len(clientState[c]) :
        Let t == clientState[c][i] IN
            /\ t[4]
            /\ \A k \in rs : store[k] = CHOOSE v \in {v | <<k, v>> \in t[1]} : TRUE

Liveness ==
    \/ \E c \in Clients, rs \subseteq Keys, ws \subseteq Keys :
        WF_<<clientState[c]>>_(\lambda t: t[4])
    \/ \A k \in Keys, t \in Seq(ANY) :
        SF_<<replicaState[PrimaryMap[k]]>>_(t)

THEOREM Spec => []Serializability
THEOREM Spec => []NoLostUpdates
THEOREM Spec => []ReadYourWrites
THEOREM Spec => <>Liveness

=============================================================================