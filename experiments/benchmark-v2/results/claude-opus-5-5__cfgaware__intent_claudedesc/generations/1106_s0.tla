---------------------------- MODULE SpanTree ----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Proc, NoPrnt, root, nbrs

(***************************************************************************)
(* Concrete values used by the model-checking configuration.               *)
(* nbrs is a set of undirected edges, each a 2-element set of processes,   *)
(* so the neighbor relation is symmetric by construction.                  *)
(***************************************************************************)
ProcVal   == {1, 2, 3, 4}
NoPrntVal == 0
rootVal   == 1
nbrsVal   == { {1, 2}, {2, 3}, {3, 4}, {1, 3} }

ASSUME NoPrntAssump == NoPrnt \notin Proc
ASSUME RootAssump   == root \in Proc
ASSUME NbrsAssump   == /\ nbrs \subseteq SUBSET Proc
                       /\ \A e \in nbrs : Cardinality(e) = 2

(***************************************************************************)
(* The neighbors of process i.                                             *)
(***************************************************************************)
Nbrs(i) == {j \in Proc : {i, j} \in nbrs}

VARIABLES prnt, rpt, msg
vars == <<prnt, rpt, msg>>

TypeOK == /\ prnt \in [Proc -> Proc \cup {NoPrnt}]
          /\ rpt  \in [Proc -> BOOLEAN]
          /\ msg  \subseteq (Proc \X Proc)

(***************************************************************************)
(* Initially no process has a parent; the root never gets one.  No         *)
(* reports have been made and no messages are in transit.                  *)
(***************************************************************************)
Init == /\ prnt = [i \in Proc |-> NoPrnt]
        /\ rpt  = [i \in Proc |-> FALSE]
        /\ msg  = {}

(***************************************************************************)
(* A process is in the tree if it is the root or has selected a parent.    *)
(***************************************************************************)
InTree(i) == (i = root) \/ (prnt[i] # NoPrnt)

(***************************************************************************)
(* A process in the tree sends a message to a neighbor (once per edge      *)
(* direction; messages are never lost since msg only grows).               *)
(***************************************************************************)
SendMsg(i, j) == /\ InTree(i)
                 /\ j \in Nbrs(i)
                 /\ <<i, j>> \notin msg
                 /\ msg' = msg \cup {<<i, j>>}
                 /\ UNCHANGED <<prnt, rpt>>

(***************************************************************************)
(* A non-root process with no parent receives a message from neighbor j   *)
(* and adopts j as its parent.                                             *)
(***************************************************************************)
Update(i, j) == /\ i # root
                /\ prnt[i] = NoPrnt
                /\ <<j, i>> \in msg
                /\ prnt' = [prnt EXCEPT ![i] = j]
                /\ UNCHANGED <<rpt, msg>>

(***************************************************************************)
(* A non-root process that has chosen its parent reports (acknowledges)    *)
(* its participation in the tree.                                          *)
(***************************************************************************)
Report(i) == /\ i # root
             /\ prnt[i] # NoPrnt
             /\ ~rpt[i]
             /\ rpt' = [rpt EXCEPT ![i] = TRUE]
             /\ UNCHANGED <<prnt, msg>>

Terminated == \A i \in Proc \ {root} : prnt[i] # NoPrnt /\ rpt[i]

Done == /\ Terminated
        /\ UNCHANGED vars

Next == \/ \E i \in Proc, j \in Proc : SendMsg(i, j)
        \/ \E i \in Proc, j \in Proc : Update(i, j)
        \/ \E i \in Proc : Report(i)
        \/ Done

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A i, j \in Proc : WF_vars(SendMsg(i, j))
        /\ \A i, j \in Proc : WF_vars(Update(i, j))
        /\ \A i \in Proc : WF_vars(Report(i))

(***************************************************************************)
(* Correctness properties.                                                 *)
(***************************************************************************)
RECURSIVE Ancestors(_, _)
Ancestors(i, n) == IF n = 0 \/ prnt[i] = NoPrnt THEN {}
                   ELSE {prnt[i]} \cup Ancestors(prnt[i], n - 1)

\* Distance-bounded reachability in the network graph
RECURSIVE ReachN(_)
ReachN(n) == IF n = 0 THEN {root}
             ELSE LET R == ReachN(n - 1)
                  IN  R \cup {j \in Proc : \E k \in R : j \in Nbrs(k)}

Reachable == ReachN(Cardinality(Proc))

RootNoParent == prnt[root] = NoPrnt

ParentIsNbr == \A i \in Proc : prnt[i] # NoPrnt => prnt[i] \in Nbrs(i)

NoCycle == \A i \in Proc : i \notin Ancestors(i, Cardinality(Proc))

\* Every process with a parent has a parent chain leading to the root
ChainToRoot == \A i \in Proc \ {root} :
                  prnt[i] # NoPrnt => root \in Ancestors(i, Cardinality(Proc))

ReportOnlyWithParent == \A i \in Proc : rpt[i] => prnt[i] # NoPrnt

Safety == /\ TypeOK
          /\ RootNoParent
          /\ ParentIsNbr
          /\ NoCycle
          /\ ChainToRoot
          /\ ReportOnlyWithParent

SpanningTree == /\ RootNoParent
                /\ \A i \in Reachable \ {root} :
                      /\ prnt[i] \in Nbrs(i)
                      /\ root \in Ancestors(i, Cardinality(Proc))

Termination == <>Terminated

EventuallySpanningTree == <>[]SpanningTree
=============================================================================