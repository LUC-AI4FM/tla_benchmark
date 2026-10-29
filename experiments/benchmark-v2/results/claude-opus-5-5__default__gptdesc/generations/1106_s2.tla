------------------------------- MODULE MC_spanning -------------------------------
(***************************************************************************)
(* Apalache-typed version of the spanning-tree specification, with        *)
(* concrete constant values. The spanning-tree algorithm is written out    *)
(* inline so that this module parses on its own.                           *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS
    \* @type: Set(Int);
    Proc,
    \* @type: Int;
    root,
    \* @type: Int;
    NoPrnt,
    \* @type: Set(<<Int, Int>>);
    nbrs

VARIABLES
    \* @type: Int -> Int;
    prnt,
    \* @type: Int -> Bool;
    rpt,
    \* @type: Set(<<Int, Int>>);
    msg

vars == <<prnt, rpt, msg>>

(***************************************************************************)
(* Concrete constant values (Apalache --cinit=ConstInit).                  *)
(***************************************************************************)
ConstInit ==
    /\ Proc = {0, 1, 2, 3}
    /\ root = 0
    /\ NoPrnt = -1
    /\ nbrs = { <<0, 1>>, <<1, 0>>,
                <<0, 2>>, <<2, 0>>,
                <<1, 3>>, <<3, 1>>,
                <<2, 3>>, <<3, 2>> }

ASSUME root \in Proc
ASSUME NoPrnt \notin Proc
ASSUME nbrs \subseteq Proc \X Proc

(***************************************************************************)
(* Algorithm                                                               *)
(***************************************************************************)
Init ==
    /\ prnt = [i \in Proc |-> NoPrnt]
    /\ rpt  = [i \in Proc |-> FALSE]
    /\ msg  = {}

\* A process may send to its neighbors once it has joined the tree.
Joined(i) == i = root \/ prnt[i] # NoPrnt

Send(i, k) ==
    /\ Joined(i)
    /\ <<i, k>> \in nbrs
    /\ <<i, k>> \notin msg
    /\ msg' = msg \cup {<<i, k>>}
    /\ UNCHANGED <<prnt, rpt>>

\* A non-root process without a parent adopts the sender of a received message.
Adopt(i, j) ==
    /\ i # root
    /\ prnt[i] = NoPrnt
    /\ <<j, i>> \in msg
    /\ prnt' = [prnt EXCEPT ![i] = j]
    /\ UNCHANGED <<rpt, msg>>

\* A joined process reports after it has sent to all of its neighbors.
Report(i) ==
    /\ Joined(i)
    /\ ~rpt[i]
    /\ \A k \in Proc : <<i, k>> \in nbrs => <<i, k>> \in msg
    /\ rpt' = [rpt EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<prnt, msg>>

Next ==
    \/ \E i, k \in Proc : Send(i, k)
    \/ \E i, j \in Proc : Adopt(i, j)
    \/ \E i \in Proc : Report(i)

Fairness ==
    /\ \A i, k \in Proc : WF_vars(Send(i, k))
    /\ \A i, j \in Proc : WF_vars(Adopt(i, j))
    /\ \A i \in Proc : WF_vars(Report(i))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)
TypeOK ==
    /\ prnt \in [Proc -> Proc \cup {NoPrnt}]
    /\ rpt \in [Proc -> BOOLEAN]
    /\ msg \subseteq nbrs

RootHasNoParent == prnt[root] = NoPrnt

ParentIsNeighbor ==
    \A i \in Proc : prnt[i] # NoPrnt => <<prnt[i], i>> \in nbrs

ReportImpliesJoined ==
    \A i \in Proc : rpt[i] => Joined(i)

MessagesFromJoined ==
    \A m \in msg : Joined(m[1])

Inv ==
    /\ TypeOK
    /\ RootHasNoParent
    /\ ParentIsNeighbor
    /\ ReportImpliesJoined
    /\ MessagesFromJoined

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)
AllJoin == <>(\A i \in Proc : Joined(i))

AllReport == <>(\A i \in Proc : rpt[i])

THEOREM Spec => []Inv
=============================================================================