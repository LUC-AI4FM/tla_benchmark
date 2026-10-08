------------------------------- MODULE KeyValueStore -------------------------------

CONSTANTS 
    Clients, Keys, PrimaryMap \* Clients = {C1, C2}, Keys = {K1, K2}

VARIABLES 
    store, clientState, replicaState, messageQueue

\* Client states: {idle, reading, writing, committing, aborted}
\* Replica states: {idle, processing}

\* Initial state
Init == /\ store = [k \in Keys |-> 0]
        /\ clientState = [c \in Clients |-> [state |-> "idle", readSet |-> {}, writeSet |-> {}]]
        /\ replicaState = [k \in Keys |-> "idle"]
        /\ messageQueue = << >>

\* Message format: <<sender, receiver, type, data>>
\* Types: "readRequest", "writeRequest", "commitRequest", "abortRequest", "readResponse", "writeResponse", "commitResponse"

\* Actions

ReadAction(c) == 
    LET readSet \in SUBSET Keys
    IN /\ clientState' = [clientState EXCEPT ![c].state = "reading", ![c].readSet = readSet]
       /\ messageQueue' = Append(messageQueue, <<c, PrimaryMap[CHOOSE k \in readSet], "readRequest", readSet>>)

WriteAction(c) == 
    LET writeSet \in SUBSET Keys
    IN /\ clientState' = [clientState EXCEPT ![c].state = "writing", ![c].writeSet = writeSet]
       /\ messageQueue' = Append(messageQueue, <<c, PrimaryMap[CHOOSE k \in writeSet], "writeRequest", writeSet>>)

CommitAction(c) == 
    /\ clientState[c].state = "writing"
    /\ messageQueue' = Append(messageQueue, <<c, PrimaryMap[CHOOSE k \in clientState[c].writeSet], "commitRequest", clientState[c].writeSet>>)
    /\ clientState' = [clientState EXCEPT ![c].state = "committing"]

AbortAction(c) == 
    /\ clientState[c].state \in {"writing", "reading"}
    /\ clientState' = [clientState EXCEPT ![c].state = "aborted"]

ProcessReadRequest(k, c) ==
    /\ replicaState[k] = "idle"
    /\ replicaState' = [replicaState EXCEPT ![k] = "processing"]
    /\ messageQueue' = Append(messageQueue, <<PrimaryMap[k], c, "readResponse", store>>)

ProcessWriteRequest(k, c, writeSet) ==
    /\ replicaState[k] = "idle"
    /\ replicaState' = [replicaState EXCEPT ![k] = "processing"]
    /\ messageQueue' = Append(messageQueue, <<PrimaryMap[k], c, "writeResponse", TRUE>>)

ProcessCommitRequest(k, c, writeSet) ==
    /\ replicaState[k] = "processing"
    /\ replicaState' = [replicaState EXCEPT ![k] = "idle"]
    /\ store' = [store EXCEPT ![k] = store[k] + 1 \* Simulate writing]
    /\ messageQueue' = Append(messageQueue, <<PrimaryMap[k], c, "commitResponse", TRUE>>)

ProcessAbortRequest(k, c) ==
    /\ replicaState[k] = "processing"
    /\ replicaState' = [replicaState EXCEPT ![k] = "idle"]
    /\ messageQueue' = Append(messageQueue, <<PrimaryMap[k], c, "abortResponse", TRUE>>)

HandleMessage == 
    LET msg \in messageQueue
        sender \in Clients \cup Keys,
        receiver \in Clients \cup Keys,
        type \in {"readRequest", "writeRequest", "commitRequest", "abortRequest", "readResponse", "writeResponse", "commitResponse"},
        data \in [Keys -> Int] \cup SUBSET Keys
    IN /\ msg = <<sender, receiver, type, data>>
       /\ \/ /\ sender \in Clients
              /\ receiver \in Keys
              /\ \/ type = "readRequest"
                 \/ type = "writeRequest"
                 \/ type = "commitRequest"
                 \/ type = "abortRequest"
           \/ /\ sender \in Keys
              /\ receiver \in Clients
              /\ \/ type = "readResponse"
                 \/ type = "writeResponse"
                 \/ type = "commitResponse"
       /\ messageQueue' = Tail(messageQueue)
       /\ CASE type = "readRequest" -> ProcessReadRequest(receiver, sender)
          [] type = "writeRequest" -> ProcessWriteRequest(receiver, sender, data)
          [] type = "commitRequest" -> ProcessCommitRequest(receiver, sender, data)
          [] type = "abortRequest" -> ProcessAbortRequest(receiver, sender)

Next == 
    \/ \E c \in Clients : clientState[c].state = "idle" /\ ReadAction(c)
    \/ \E c \in Clients : clientState[c].state = "writing" /\ CommitAction(c)
    \/ \E c \in Clients : clientState[c].state \in {"reading", "writing"} /\ AbortAction(c)
    \/ HandleMessage

Spec == Init /\ [][Next]_<<store, clientState, replicaState, messageQueue>>

\* Safety properties
Serializability ==
    \A s1, s2 \in StateTrace : 
        \E pi \in Permutations(CommittedTransactions(s1)) :
            \A t \in CommittedTransactions(s2) :
                \E i \in 1..Len(pi) :
                    Serial(t, pi[i])

NoLostUpdates ==
    \A s \in StateTrace, c \in Clients, k \in Keys :
        \E v \in Int :
            \A t \in TransactionsByClient(s, c) :
                (k \notin t.writeSet \/ store[k] = v)

ReadYourWrites ==
    \A s \in StateTrace, c \in Clients, k \in Keys :
        \A t1, t2 \in TransactionsByClient(s, c) :
            (t1.state = "committed" /\ k \in t1.writeSet /\ t2.state = "reading" /\ k \in t2.readSet)
                => store[k] = v

\* Liveness properties
BoundedRetries ==
    \A s \in StateTrace, c \in Clients :
        WF_s_<<c>>[Next]

Progress ==
    \A s \in StateTrace :
        \E pi \in Permutations(CommittedTransactions(s)) :
            \A t \in CommittedTransactions(s) :
                \E i \in 1..Len(pi) :
                    Serial(t, pi[i])

=============================================================================