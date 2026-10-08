--------------------------- MODULE DistributedLedger ---------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
  Clients,        \* Set of clients
  MaxView,        \* Maximum view id (natural number, defines 0..MaxView)
  MaxSeq,         \* Maximum sequence number per view (natural number)
  UseAltInit      \* BOOLEAN: if TRUE, start from alternative mid-execution state

(*
  Universe definitions
*)
VIEWS == 0..MaxView
SEQ   == 1..MaxSeq
NextSeqDom == 1..(MaxSeq + 1)

TxIDs == { [v |-> v, s |-> s] : v \in VIEWS, s \in SEQ }

None       == "None"
NoneClient == "NoneClient"

(*
  State variables
*)
VARIABLES
  usedViews,    \* subset of VIEWS that are active (have been created)
  base,         \* [VIEWS -> TxIDs \cup {None}]: base tx each view starts from (for s=1)
  nextSeq,      \* [VIEWS -> NextSeqDom]: next sequence to assign in each view
  status,       \* [TxIDs -> {"none","proposed","committed"}]
  issuer,       \* [TxIDs -> Clients \cup {NoneClient}]
  obs,          \* [TxIDs -> SUBSET TxIDs], observed prior txs reported in response
  parent,       \* [TxIDs -> TxIDs \cup {None}], parent pointer (defines branch DAG)
  pendingReq,   \* SUBSET Clients: clients with pending request (no response yet)
  respTx,       \* [Clients -> TxIDs \cup {None}]: txid assigned in response (if any)
  respObs,      \* [Clients -> SUBSET TxIDs]: observed set echoed in the response
  notif         \* [Clients -> SUBSET TxIDs]: committed txs the client has been notified about

vars == << usedViews, base, nextSeq, status, issuer, obs, parent, pendingReq, respTx, respObs, notif >>

(*
  Helper definitions
*)
Committed == { t \in TxIDs : status[t] = "committed" }
Proposed  == { t \in TxIDs : status[t] = "proposed" }
TxCreated == { t \in TxIDs : status[t] # "none" }

RECURSIVE Ancestors(_)
Ancestors(t) ==
  IF t \in TxIDs /\ parent[t] \in TxIDs
  THEN { parent[t] } \cup Ancestors(parent[t])
  ELSE {}

Comparable(x, y) == x = y \/ x \in Ancestors(y) \/ y \in Ancestors(x)

ConsistentSet(S) == \A x \in S: \A y \in S: Comparable(x, y)

(*
  Initial states
*)
EmptyInit ==
  /\ usedViews = {0}
  /\ base     = [ v \in VIEWS |-> None ]
  /\ nextSeq  = [ v \in VIEWS |-> 1 ]
  /\ status   = [ t \in TxIDs |-> "none" ]
  /\ issuer   = [ t \in TxIDs |-> NoneClient ]
  /\ obs      = [ t \in TxIDs |-> {} ]
  /\ parent   = [ t \in TxIDs |-> None ]
  /\ pendingReq = {}
  /\ respTx   = [ c \in Clients |-> None ]
  /\ respObs  = [ c \in Clients |-> {} ]
  /\ notif    = [ c \in Clients |-> {} ]

AltInit ==
  LET T01 == [v |-> 0, s |-> 1]
      T02 == [v |-> 0, s |-> 2]
      T11 == [v |-> 1, s |-> 1]
      T12 == [v |-> 1, s |-> 2]
      C1  == CHOOSE c \in Clients : TRUE
      HasSecond == \E d \in Clients : d # C1
      C2  == CHOOSE d \in Clients : d \in Clients /\ d # C1
  IN
  /\ usedViews = {0, 1}
  /\ base     = [ v \in VIEWS |-> None ] EXCEPT ![1] = T01
  /\ nextSeq  = [ v \in VIEWS |-> 1 ] EXCEPT ![0] = 3, ![1] = 3
  /\ status   = [ t \in TxIDs |->
                    IF t = T01 \/ t = T02 \/ t = T11 THEN "committed"
                    ELSE IF t = T12 THEN "proposed" ELSE "none" ]
  /\ issuer   = [ t \in TxIDs |->
                    IF t = T12 THEN C1 ELSE NoneClient ]
  /\ obs      = [ t \in TxIDs |->
                    IF t = T12 THEN {T01, T11} ELSE {} ]
  /\ parent   = [ t \in TxIDs |-> None ]
                EXCEPT ![T01] = None,
                       ![T02] = T01,
                       ![T11] = T01,
                       ![T12] = T11
  /\ pendingReq = IF HasSecond THEN {C2} ELSE {}
  /\ respTx   = [ c \in Clients |->
                    IF c = C1 THEN T12 ELSE None ]
  /\ respObs  = [ c \in Clients |->
                    IF c = C1 THEN {T01, T11} ELSE {} ]
  /\ notif    = [ c \in Clients |-> {} ]

Init == IF UseAltInit THEN AltInit ELSE EmptyInit

(*
  Actions
*)
Submit(c) ==
  /\ c \in Clients
  /\ c \notin pendingReq
  /\ respTx[c] = None
  /\ pendingReq' = pendingReq \cup {c}
  /\ UNCHANGED << usedViews, base, nextSeq, status, issuer, obs, parent, respTx, respObs, notif >>

CreateView(v, b) ==
  /\ v \in VIEWS \ usedViews
  /\ b \in (Committed \cup {None})
  /\ usedViews' = usedViews \cup {v}
  /\ base'    = [ base EXCEPT ![v] = b ]
  /\ nextSeq' = [ nextSeq EXCEPT ![v] = 1 ]
  /\ UNCHANGED << status, issuer, obs, parent, pendingReq, respTx, respObs, notif >>

Respond(c, v) ==
  /\ c \in pendingReq
  /\ v \in usedViews
  /\ nextSeq[v] \in SEQ
  /\ LET s == nextSeq[v]
         t == [v |-> v, s |-> s]
         os == CHOOSE S \in SUBSET Committed : ConsistentSet(S)
     IN
     /\ pendingReq' = pendingReq \ {c}
     /\ respTx'  = [ respTx EXCEPT ![c] = t ]
     /\ respObs' = [ respObs EXCEPT ![c] = os ]
     /\ issuer'  = [ issuer EXCEPT ![t] = c ]
     /\ status'  = [ status EXCEPT ![t] = "proposed" ]
     /\ obs'     = [ obs EXCEPT ![t] = os ]
     /\ parent'  = [ parent EXCEPT ![t] = IF s = 1 THEN base[v] ELSE [v |-> v, s |-> s - 1] ]
     /\ nextSeq' = [ nextSeq EXCEPT ![v] = s + 1 ]
     /\ UNCHANGED << usedViews, base, notif >>

RespondClient(c) == \E v \in VIEWS: Respond(c, v)

Commit(t) ==
  /\ t \in TxIDs
  /\ status[t] = "proposed"
  /\ parent[t] = None \/ status[parent[t]] = "committed"
  /\ status' = [ status EXCEPT ![t] = "committed" ]
  /\ UNCHANGED << usedViews, base, nextSeq, issuer, obs, parent, pendingReq, respTx, respObs, notif >>

CommitTx(t) == Commit(t)

Notify(c, t) ==
  /\ c \in Clients
  /\ t \in TxIDs
  /\ issuer[t] = c
  /\ status[t] = "committed"
  /\ t \notin notif[c]
  /\ notif' = [ notif EXCEPT ![c] = @ \cup {t} ]
  /\ UNCHANGED << usedViews, base, nextSeq, status, issuer, obs, parent, pendingReq, respTx, respObs >>

Next ==
  \E c \in Clients: Submit(c)
  \/ \E v \in VIEWS: \E b \in (Committed \cup {None}): CreateView(v, b)
  \/ \E c \in Clients: RespondClient(c)
  \/ \E t \in TxIDs: Commit(t)
  \/ \E c \in Clients: \E t \in TxIDs: Notify(c, t)

(*
  Safety invariants
*)
TypeInv ==
  /\ usedViews \subseteq VIEWS
  /\ base \in [ VIEWS -> (TxIDs \cup {None}) ]
  /\ nextSeq \in [ VIEWS -> NextSeqDom ]
  /\ status \in [ TxIDs -> {"none","proposed","committed"} ]
  /\ issuer \in [ TxIDs -> (Clients \cup {NoneClient}) ]
  /\ obs \in [ TxIDs -> SUBSET TxIDs ]
  /\ parent \in [ TxIDs -> (TxIDs \cup {None}) ]
  /\ pendingReq \subseteq Clients
  /\ respTx \in [ Clients -> (TxIDs \cup {None}) ]
  /\ respObs \in [ Clients -> SUBSET TxIDs ]
  /\ notif \in [ Clients -> SUBSET TxIDs ]

ParentWellFormed ==
  \A v \in VIEWS:
    \A s \in SEQ:
      LET t == [v |-> v, s |-> s] IN
        status[t] # "none" =>
          parent[t] = (IF s = 1 THEN base[v] ELSE [v |-> v, s |-> s - 1])

BaseCommitted ==
  \A v \in usedViews: base[v] = None \/ base[v] \in Committed

ParentCommitted ==
  \A t \in Committed: parent[t] = None \/ parent[t] \in Committed

ObsConsistency ==
  \A t \in TxCreated:
    /\ obs[t] \subseteq Committed
    /\ ConsistentSet(obs[t])

ReadConsistency ==
  \A t \in Committed: obs[t] \subseteq Ancestors(t)

NoCycleCommitted ==
  \A t \in Committed: t \notin Ancestors(t)

WithinViewCommitPrefix ==
  \A v \in VIEWS:
    \A s \in SEQ:
      status[[v |-> v, s |-> s]] = "committed"
        => (s = 1) \/ status[[v |-> v, s |-> s - 1]] = "committed"

Safety == TypeInv /\ ParentWellFormed /\ BaseCommitted /\ ParentCommitted /\ ObsConsistency /\ ReadConsistency /\ NoCycleCommitted /\ WithinViewCommitPrefix

(*
  Liveness properties (for model checking)
*)
ResponseProgress ==
  \A c \in Clients: []( c \in pendingReq => <> (respTx[c] # None) )

CommitProgress ==
  \A t \in TxIDs:
    [] ( (status[t] = "proposed" /\ (parent[t] = None \/ status[parent[t]] = "committed"))
         => <> (status[t] = "committed") )

(*
  Fairness conditions
*)
Fairness ==
  /\ \A c \in Clients: SF_vars(RespondClient(c))
  /\ \A t \in TxIDs: WF_vars(CommitTx(t))

Spec == Init /\ [][Next]_vars /\ Fairness

=============================================================================