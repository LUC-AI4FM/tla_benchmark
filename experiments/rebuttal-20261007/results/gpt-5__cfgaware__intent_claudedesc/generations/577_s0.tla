------------------------------- MODULE MultiNodeLedger -------------------------------
EXTENDS Naturals

(*
  Distributed ledger with multiple branches (per-node heads), read-write transactions,
  responses carrying observed prior transactions, and commit notifications.
  This module provides an alternative initial state AltInit and a model-checking
  harness MCSpecMultiNodeReadsAlt that starts from AltInit.
*)

CONSTANTS
  CLIENTS,   \* Set of clients
  NODES,     \* Set of nodes
  VIEWS,     \* Set of view identifiers
  SEQS       \* Set of sequence identifiers

NoClient == "NoClient"
None == "None"
G == "G"

TXIDS == VIEWS \X SEQS

StatusVals == {"absent","pending","committed"}

(*
  State variables
*)
VARIABLES
  Status,        \* [TXIDS -> StatusVals]
  Parent,        \* [TXIDS -> (TXIDS \cup {G} \cup {None})]
  RespObserved,  \* [TXIDS -> SUBSET TXIDS]
  TxClient,      \* [TXIDS -> (CLIENTS \cup {NoClient})]
  NodeHead,      \* [NODES -> (TXIDS \cup {G})]
  OutTx,         \* [CLIENTS -> (TXIDS \cup {None})]
  PendingReq,    \* [CLIENTS -> BOOLEAN]
  Notified       \* [CLIENTS -> SUBSET TXIDS]

Vars == << Status, Parent, RespObserved, TxClient, NodeHead, OutTx, PendingReq, Notified >>

(*
  Basic helpers
*)
TxExists(t) == Status[t] # "absent"
Committed == { t \in TXIDS : Status[t] = "committed" }
Pending == { t \in TXIDS : Status[t] = "pending" }

RECURSIVE Ancestors(_)
Ancestors(t) ==
  IF Parent[t] \in TXIDS
  THEN {Parent[t]} \cup Ancestors(Parent[t])
  ELSE {}

TxsOnNodeBranch(n) ==
  IF NodeHead[n] \in TXIDS
  THEN {NodeHead[n]} \cup Ancestors(NodeHead[n])
  ELSE {}

(*
  Type correctness
*)
TypeOK ==
  /\ Status \in [TXIDS -> StatusVals]
  /\ Parent \in [TXIDS -> (TXIDS \cup {G} \cup {None})]
  /\ RespObserved \in [TXIDS -> SUBSET TXIDS]
  /\ TxClient \in [TXIDS -> (CLIENTS \cup {NoClient})]
  /\ NodeHead \in [NODES -> (TXIDS \cup {G})]
  /\ OutTx \in [CLIENTS -> (TXIDS \cup {None})]
  /\ PendingReq \in [CLIENTS -> BOOLEAN]
  /\ Notified \in [CLIENTS -> SUBSET TXIDS]

(*
  Initial states
*)
Init ==
  /\ Status = [t \in TXIDS |-> "absent"]
  /\ Parent = [t \in TXIDS |-> None]
  /\ RespObserved = [t \in TXIDS |-> {}]
  /\ TxClient = [t \in TXIDS |-> NoClient]
  /\ NodeHead = [n \in NODES |-> G]
  /\ OutTx = [c \in CLIENTS |-> None]
  /\ PendingReq = [c \in CLIENTS |-> FALSE]
  /\ Notified = [c \in CLIENTS |-> {}]

(*
  Alternative initial states:
  - Some transactions already exist (pending/committed)
  - Multiple branches exist
  - Some transactions already responded and/or committed
*)
RECURSIVE AncestorsOf(_,_)
AncestorsOf(P, t) ==
  IF P[t] \in TXIDS
  THEN {P[t]} \cup AncestorsOf(P, P[t])
  ELSE {}

AltInit ==
  \E E \in SUBSET TXIDS,
    P \in [TXIDS -> (TXIDS \cup {G} \cup {None})],
    S \in [TXIDS -> StatusVals],
    R \in [TXIDS -> SUBSET TXIDS],
    T \in [TXIDS -> (CLIENTS \cup {NoClient})],
    NH \in [NODES -> (TXIDS \cup {G})],
    OT \in [CLIENTS -> (TXIDS \cup {None})],
    PR \in [CLIENTS -> BOOLEAN],
    NF \in [CLIENTS -> SUBSET TXIDS]:
    /\ Status = S
    /\ Parent = P
    /\ RespObserved = R
    /\ TxClient = T
    /\ NodeHead = NH
    /\ OutTx = OT
    /\ PendingReq = PR
    /\ Notified = NF
    /\ TypeOK
    /\ \A t \in TXIDS: (S[t] # "absent") <=> (t \in E)
    /\ \A t \in E:
         /\ P[t] \in TXIDS \cup {G}
         /\ (P[t] \in TXIDS => S[P[t]] # "absent")
    /\ \A t \in (TXIDS \ E): P[t] = None
    /\ \A t \in E: R[t] \subseteq AncestorsOf(P, t)
    /\ \A t \in E: ~(t \in AncestorsOf(P, t))  \* acyclicity
    /\ \A n \in NODES: NH[n] = G \/ NH[n] \in E
    /\ \A t \in TXIDS:
         S[t] = "committed" =>
           (P[t] = G \/ (P[t] \in TXIDS /\ S[P[t]] = "committed"))
    /\ \E t \in TXIDS: S[t] = "committed"                     \* some committed
    /\ \E t1, t2 \in E: t1 # t2 /\ ~(t1 \in AncestorsOf(P, t2)) /\ ~(t2 \in AncestorsOf(P, t1))  \* multiple branches
    /\ \E t \in E: T[t] \in CLIENTS                           \* at least one responded tx
    /\ \A c \in CLIENTS:
         OT[c] = None \/
         (OT[c] \in E /\ T[OT[c]] = c)
    /\ \A c \in CLIENTS:
         NF[c] \subseteq { t \in TXIDS : S[t] = "committed" /\ T[t] = c }

(*
  Actions
*)

Request ==
  \E c \in CLIENTS:
    /\ PendingReq[c] = FALSE
    /\ OutTx[c] = None
    /\ PendingReq' = [PendingReq EXCEPT ![c] = TRUE]
    /\ UNCHANGED << Status, Parent, RespObserved, TxClient, NodeHead, OutTx, Notified >>

Respond ==
  \E c \in CLIENTS:
  \E n \in NODES:
  \E t \in TXIDS:
  \E obs \in SUBSET TXIDS:
    LET parent == NodeHead[n] IN
    /\ PendingReq[c] = TRUE
    /\ Status[t] = "absent"
    /\ parent \in (TXIDS \cup {G})
    /\ (parent = G \/ (parent \in TXIDS /\ TxExists(parent)))
    /\ obs \subseteq (IF parent \in TXIDS THEN {parent} \cup Ancestors(parent) ELSE {})
    /\ Status' = [Status EXCEPT ![t] = "pending"]
    /\ Parent' = [Parent EXCEPT ![t] = parent]
    /\ RespObserved' = [RespObserved EXCEPT ![t] = obs]
    /\ TxClient' = [TxClient EXCEPT ![t] = c]
    /\ NodeHead' = [NodeHead EXCEPT ![n] = t]
    /\ OutTx' = [OutTx EXCEPT ![c] = t]
    /\ PendingReq' = [PendingReq EXCEPT ![c] = FALSE]
    /\ UNCHANGED Notified

Commit ==
  \E t \in TXIDS:
    /\ Status[t] = "pending"
    /\ (Parent[t] = G \/ (Parent[t] \in TXIDS /\ Status[Parent[t]] = "committed"))
    /\ Status' = [Status EXCEPT ![t] = "committed"]
    /\ UNCHANGED << Parent, RespObserved, TxClient, NodeHead, OutTx, PendingReq, Notified >>

Notify ==
  \E c \in CLIENTS:
  \E t \in TXIDS:
    /\ Status[t] = "committed"
    /\ TxClient[t] = c
    /\ ~(t \in Notified[c])
    /\ Notified' = [Notified EXCEPT ![c] = @ \cup {t}]
    /\ UNCHANGED << Status, Parent, RespObserved, TxClient, NodeHead, OutTx, PendingReq >>

HeadAdopt ==
  \E n \in NODES:
  \E t \in (TXIDS \cup {G}):
    /\ (t = G \/ TxExists(t))
    /\ NodeHead' = [NodeHead EXCEPT ![n] = t]
    /\ UNCHANGED << Status, Parent, RespObserved, TxClient, OutTx, PendingReq, Notified >>

Next ==
  Request
  \/ Respond
  \/ Commit
  \/ Notify
  \/ HeadAdopt

(*
  Correctness properties (state predicates)
*)

InvReadConsistency ==
  \A t \in TXIDS:
    TxExists(t) => RespObserved[t] \subseteq Ancestors(t)

InvBranchConsistency ==
  /\ \A t \in TXIDS:
       TxExists(t) => Parent[t] \in (TXIDS \cup {G})
  /\ \A t \in TXIDS:
       Parent[t] \in TXIDS => TxExists(Parent[t])
  /\ \A n \in NODES: NodeHead[n] \in (TXIDS \cup {G})
  /\ \A t \in TXIDS: ~(t \in Ancestors(t))  \* global acyclicity

InvSerializability ==
  \A t \in TXIDS:
    Status[t] = "committed" =>
      (Parent[t] = G \/ (Parent[t] \in TXIDS /\ Status[Parent[t]] = "committed"))

(*
  Model-checking harness starting from the alternative initial state
*)
MCSpecMultiNodeReadsAlt ==
  AltInit /\ [][Next]_Vars

=============================================================================