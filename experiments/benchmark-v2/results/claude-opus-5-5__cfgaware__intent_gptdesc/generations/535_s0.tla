---------------------------- MODULE ConcurrentTupleStore ----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS minValue, Tuples

ConstMinValue == 0
ConstTuples == { <<1, 10>>, <<2, 20>> }

Clients  == {"c1", "c2"}
MaxOps   == 2

Keys      == { t[1] : t \in Tuples }
ValDomain == { t[2] : t \in Tuples }
Capacity  == Cardinality(Keys)

InitVal(k) == (CHOOSE t \in Tuples : t[1] = k)[2]

ASSUME \A t1, t2 \in Tuples : t1[1] = t2[1] => t1 = t2
ASSUME minValue \notin ValDomain

OpNames == {"read", "update", "insert", "delete"}

NoReq  == [op |-> "none", key |-> minValue, val |-> minValue]
NoResp == [op |-> "none", key |-> minValue, val |-> minValue, ok |-> FALSE, ver |-> 0]

Requests ==
       [op : {"read"},   key : Keys, val : {minValue}]
  \cup [op : {"update"}, key : Keys, val : ValDomain]
  \cup [op : {"insert"}, key : Keys, val : ValDomain]
  \cup [op : {"delete"}, key : Keys, val : {minValue}]

VARIABLES
  present,
  store,
  version,
  writeLog,
  req,
  resp,
  pc,
  budget,
  lastResult

vars == <<present, store, version, writeLog, req, resp, pc, budget, lastResult>>

TypeOK ==
  /\ present \subseteq Keys
  /\ store \in [Keys -> ValDomain]
  /\ version \in [Keys -> Nat]
  /\ pc \in [Clients -> {"idle", "waiting", "done"}]
  /\ budget \in [Clients -> 0..MaxOps]
  /\ req \in [Clients -> Requests \cup {NoReq}]

Init ==
  /\ present = Keys
  /\ store = [k \in Keys |-> InitVal(k)]
  /\ version = [k \in Keys |-> 0]
  /\ writeLog = { <<k, 0, InitVal(k)>> : k \in Keys }
  /\ req = [c \in Clients |-> NoReq]
  /\ resp = [c \in Clients |-> NoResp]
  /\ pc = [c \in Clients |-> "idle"]
  /\ budget = [c \in Clients |-> MaxOps]
  /\ lastResult = [c \in Clients |-> NoResp]

\* Client invokes an operation: request is placed in the network
Invoke(c) ==
  /\ pc[c] = "idle"
  /\ budget[c] > 0
  /\ \E r \in Requests :
       /\ req' = [req EXCEPT ![c] = r]
       /\ pc' = [pc EXCEPT ![c] = "waiting"]
       /\ budget' = [budget EXCEPT ![c] = @ - 1]
  /\ UNCHANGED <<present, store, version, writeLog, resp, lastResult>>

\* Server processes a pending request atomically (linearization point).
\* Nondeterministic choice of which client's request is served models message delay.
Serve(c) ==
  /\ pc[c] = "waiting"
  /\ req[c] # NoReq
  /\ resp[c] = NoResp
  /\ LET r == req[c]
         k == r.key
     IN
     \/ /\ r.op = "read"
        /\ resp' = [resp EXCEPT ![c] =
              IF k \in present
                THEN [op |-> "read", key |-> k, val |-> store[k], ok |-> TRUE,  ver |-> version[k]]
                ELSE [op |-> "read", key |-> k, val |-> minValue, ok |-> FALSE, ver |-> version[k]]]
        /\ UNCHANGED <<present, store, version, writeLog>>
     \/ /\ r.op = "update"
        /\ IF k \in present
             THEN /\ store' = [store EXCEPT ![k] = r.val]
                  /\ version' = [version EXCEPT ![k] = @ + 1]
                  /\ writeLog' = writeLog \cup { <<k, version[k] + 1, r.val>> }
                  /\ resp' = [resp EXCEPT ![c] =
                        [op |-> "update", key |-> k, val |-> r.val, ok |-> TRUE, ver |-> version[k] + 1]]
             ELSE /\ resp' = [resp EXCEPT ![c] =
                        [op |-> "update", key |-> k, val |-> r.val, ok |-> FALSE, ver |-> version[k]]]
                  /\ UNCHANGED <<store, version, writeLog>>
        /\ UNCHANGED present
     \/ /\ r.op = "insert"
        /\ IF k \notin present /\ Cardinality(present) < Capacity
             THEN /\ present' = present \cup {k}
                  /\ store' = [store EXCEPT ![k] = r.val]
                  /\ version' = [version EXCEPT ![k] = @ + 1]
                  /\ writeLog' = writeLog \cup { <<k, version[k] + 1, r.val>> }
                  /\ resp' = [resp EXCEPT ![c] =
                        [op |-> "insert", key |-> k, val |-> r.val, ok |-> TRUE, ver |-> version[k] + 1]]
             ELSE /\ resp' = [resp EXCEPT ![c] =
                        [op |-> "insert", key |-> k, val |-> r.val, ok |-> FALSE, ver |-> version[k]]]
                  /\ UNCHANGED <<present, store, version, writeLog>>
     \/ /\ r.op = "delete"
        /\ IF k \in present
             THEN /\ present' = present \ {k}
                  /\ resp' = [resp EXCEPT ![c] =
                        [op |-> "delete", key |-> k, val |-> minValue, ok |-> TRUE, ver |-> version[k]]]
             ELSE /\ UNCHANGED present
                  /\ resp' = [resp EXCEPT ![c] =
                        [op |-> "delete", key |-> k, val |-> minValue, ok |-> FALSE, ver |-> version[k]]]
        /\ UNCHANGED <<store, version, writeLog>>
  /\ UNCHANGED <<req, pc, budget, lastResult>>

\* Client receives the (possibly delayed) response and completes the operation
Complete(c) ==
  /\ pc[c] = "waiting"
  /\ resp[c] # NoResp
  /\ lastResult' = [lastResult EXCEPT ![c] = resp[c]]
  /\ resp' = [resp EXCEPT ![c] = NoResp]
  /\ req' = [req EXCEPT ![c] = NoReq]
  /\ pc' = [pc EXCEPT ![c] = "idle"]
  /\ UNCHANGED <<present, store, version, writeLog, budget>>

Finish(c) ==
  /\ pc[c] = "idle"
  /\ budget[c] = 0
  /\ pc' = [pc EXCEPT ![c] = "done"]
  /\ UNCHANGED <<present, store, version, writeLog, req, resp, budget, lastResult>>

Terminated ==
  /\ \A c \in Clients : pc[c] = "done"
  /\ UNCHANGED vars

ClientStep(c) == Invoke(c) \/ Complete(c) \/ Finish(c)

Next ==
  \/ \E c \in Clients : ClientStep(c) \/ Serve(c)
  \/ Terminated

Fairness ==
  \A c \in Clients :
     /\ WF_vars(Serve(c))
     /\ WF_vars(Complete(c))
     /\ WF_vars(Finish(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

UniqueKeys ==
  \A k1, k2 \in present : (k1 = k2) <=> (store[k1] = store[k2] /\ k1 = k2)

KeysWithinCapacity == Cardinality(present) <= Capacity

DomainConstraint == \A k \in Keys : store[k] \in ValDomain

NoSentinelRecord == \A k \in present : store[k] # minValue

NoSentinelObserved ==
  \A c \in Clients :
     /\ (resp[c].op = "read" /\ resp[c].ok) => resp[c].val # minValue
     /\ (lastResult[c].op = "read" /\ lastResult[c].ok) => lastResult[c].val # minValue

\* Store always reflects the latest linearized write for each key (no lost updates)
NoLostUpdates ==
  \A k \in Keys : <<k, version[k], store[k]>> \in writeLog

\* Reads return a whole value that was actually written at the observed version
NoTornReads ==
  \A c \in Clients :
     (resp[c].op = "read" /\ resp[c].ok) =>
        <<resp[c].key, resp[c].ver, resp[c].val>> \in writeLog

\* Each version of a key has exactly one value (atomic writes)
AtomicWrites ==
  \A e1, e2 \in writeLog :
     (e1[1] = e2[1] /\ e1[2] = e2[2]) => e1[3] = e2[3]

SafetyInv ==
  /\ TypeOK
  /\ KeysWithinCapacity
  /\ DomainConstraint
  /\ NoSentinelRecord
  /\ NoSentinelObserved
  /\ NoLostUpdates
  /\ NoTornReads
  /\ AtomicWrites

-----------------------------------------------------------------------------
\* Liveness properties

NoPermanentBlocking ==
  \A c \in Clients : (pc[c] = "waiting") ~> (pc[c] # "waiting")

UpdatesEventuallyVisible ==
  \A c \in Clients :
     (resp[c].op = "update" /\ resp[c].ok) ~>
        (version[resp[c].key] >= resp[c].ver \/ resp[c] = NoResp)

Termination == <>(\A c \in Clients : pc[c] = "done")

=============================================================================