------------------------------ MODULE MC_spanning ------------------------------
(***************************************************************************)
(* Apalache-typed wrapper for the spanning-tree specification.             *)
(*                                                                         *)
(* The original module is meant to be imported with                        *)
(*     S == INSTANCE spanning                                              *)
(* Here the constants and variables carry Apalache type annotations, and   *)
(* CInit supplies concrete sample values for the constants. The            *)
(* spanning-tree definitions are written out in this module so that it     *)
(* parses on its own with SANY, without needing a separate spanning.tla.   *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS
    \* @type: Set(Str);
    Proc,
    \* @type: Str;
    root,
    \* @type: Str;
    nopar,
    \* @type: Set(<<Str, Str>>);
    Nbrs

VARIABLES
    \* @type: Str -> Str;
    parent,
    \* @type: Str -> Bool;
    reported,
    \* @type: Set(<<Str, Str>>);
    msg

vars == <<parent, reported, msg>>

(***************************************************************************)
(* Concrete sample constant values (Apalache ConstInit).                   *)
(***************************************************************************)
CInit ==
    /\ Proc  = {"p1", "p2", "p3", "p4"}
    /\ root  = "p1"
    /\ nopar = "none"
    /\ Nbrs  = { <<"p1", "p2">>, <<"p2", "p1">>,
                 <<"p1", "p3">>, <<"p3", "p1">>,
                 <<"p2", "p4">>, <<"p4", "p2">>,
                 <<"p3", "p4">>, <<"p4", "p3">> }

ASSUME /\ root \in Proc
       /\ nopar \notin Proc
       /\ Nbrs \subseteq Proc \X Proc

(***************************************************************************)
(* Spanning-tree algorithm, in place of INSTANCE spanning.                 *)
(***************************************************************************)
\* @type: Str => Set(Str);
Nbr(p) == {q \in Proc : <<p, q>> \in Nbrs}

TypeOK ==
    /\ parent \in [Proc -> Proc \cup {nopar}]
    /\ reported \in [Proc -> BOOLEAN]
    /\ msg \subseteq Proc \X Proc

Init ==
    /\ parent = [p \in Proc |-> IF p = root THEN root ELSE nopar]
    /\ reported = [p \in Proc |-> FALSE]
    /\ msg = {m \in Nbrs : m[1] = root}

\* Process m[2] receives a message from m[1]
Receive(m) ==
    /\ m \in msg
    /\ LET q == m[2] IN
         IF parent[q] = nopar
           THEN /\ parent' = [parent EXCEPT ![q] = m[1]]
                /\ msg' = (msg \ {m}) \cup {<<q, r>> : r \in Nbr(q)}
           ELSE /\ msg' = msg \ {m}
                /\ UNCHANGED parent
    /\ UNCHANGED reported

\* Process p reports once it has joined the tree, has no pending
\* messages, and all of its children have reported
Report(p) ==
    /\ parent[p] # nopar
    /\ ~reported[p]
    /\ \A m \in msg : m[1] # p /\ m[2] # p
    /\ \A q \in Proc : (q # p /\ parent[q] = p) => reported[q]
    /\ reported' = [reported EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<parent, msg>>

Next ==
    \/ \E m \in msg : Receive(m)
    \/ \E p \in Proc : Report(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in Proc : WF_vars(Report(p))
    /\ WF_vars(\E m \in msg : Receive(m))

(***************************************************************************)
(* Safety and liveness properties.                                         *)
(***************************************************************************)
ParentIsNeighbor ==
    \A p \in Proc \ {root} :
        parent[p] # nopar => <<parent[p], p>> \in Nbrs

RootIsOwnParent == parent[root] = root

ReportedImpliesJoined ==
    \A p \in Proc : reported[p] => parent[p] # nopar

Inv == TypeOK /\ ParentIsNeighbor /\ RootIsOwnParent /\ ReportedImpliesJoined

\* Valid when the neighbor graph is connected (as in CInit)
AllJoin == <>(\A p \in Proc : parent[p] # nopar)

RootReports == <>(reported[root])
================================================================================