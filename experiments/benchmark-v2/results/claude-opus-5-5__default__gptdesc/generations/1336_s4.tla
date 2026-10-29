------------------------------- MODULE MCEcho -------------------------------
(***************************************************************************)
(* A tiny, fully connected, undirected graph with three nodes "a", "b",   *)
(* and "c", used to model check the Echo algorithm. The Echo algorithm is *)
(* included here so that the module is self-contained.                    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences, TLC

(***************************************************************************)
(* Graph definitions                                                       *)
(***************************************************************************)

\* Nodes as an explicit set.
N1 == {"a", "b", "c"}

\* Nodes as the domain of a function.
NodesF == DOMAIN [n \in {"a", "b", "c"} |-> TRUE]

\* An explicit, fully connected, symmetric, irreflexive edge relation.
R1 == { <<"a", "b">>, <<"b", "a">>,
        <<"a", "c">>, <<"c", "a">>,
        <<"b", "c">>, <<"c", "b">> }

\* The edge relation given as a neighbour function.
RF == [n \in N1 |-> N1 \ {n}]

\* Properties of a relation r over a node set N.
IsIrreflexive(r, N) == \A n \in N : <<n, n>> \notin r

IsSymmetric(r, N) == \A m, n \in N : <<m, n>> \in r => <<n, m>> \in r

\* There is a path of edges in r from x to y of length at most |N|.
PathExists(r, N, x, y) ==
    \E k \in 1..Cardinality(N) :
        \E p \in [1..(k+1) -> N] :
            /\ p[1] = x
            /\ p[k+1] = y
            /\ \A i \in 1..k : <<p[i], p[i+1]>> \in r

IsConnected(r, N) ==
    \A x, y \in N : x = y \/ PathExists(r, N, x, y)

\* A relation chosen by CHOOSE that is connected, symmetric, and irreflexive.
RChoose == CHOOSE r \in SUBSET (N1 \X N1) :
               /\ IsConnected(r, N1)
               /\ IsSymmetric(r, N1)
               /\ IsIrreflexive(r, N1)

\* The instantiation used for model checking.
Nodes     == N1
R         == RChoose
initiator == "a"
NoNode    == "none"

ASSUME /\ NodesF = N1
       /\ IsConnected(R1, N1) /\ IsSymmetric(R1, N1) /\ IsIrreflexive(R1, N1)
       /\ initiator \in N1
       /\ NoNode \notin N1

Neighbors(n) == {m \in Nodes : <<n, m>> \in R}

(***************************************************************************)
(* The Echo algorithm                                                      *)
(***************************************************************************)
VARIABLES inbox,   \* inbox[n] : set of nodes from which n has a pending message
          rcvd,    \* rcvd[n]  : set of neighbours n has received a message from
          parent   \* parent[n]: the parent of n in the spanning tree

vars == <<inbox, rcvd, parent>>

TypeOK ==
    /\ inbox  \in [Nodes -> SUBSET Nodes]
    /\ rcvd   \in [Nodes -> SUBSET Nodes]
    /\ parent \in [Nodes -> Nodes \cup {NoNode}]

Init ==
    /\ inbox  = [n \in Nodes |-> IF n \in Neighbors(initiator)
                                    THEN {initiator} ELSE {}]
    /\ rcvd   = [n \in Nodes |-> {}]
    /\ parent = [n \in Nodes |-> IF n = initiator THEN initiator ELSE NoNode]

Receive(n) ==
    \E m \in inbox[n] :
        LET first   == rcvd[n] = {} /\ n # initiator
            newPar  == IF first THEN m ELSE parent[n]
            newRcvd == rcvd[n] \cup {m}
            fwd     == IF first THEN Neighbors(n) \ {m} ELSE {}
            echo    == IF n # initiator /\ newRcvd = Neighbors(n)
                          THEN {newPar} ELSE {}
            targets == fwd \cup echo
        IN  /\ rcvd'   = [rcvd EXCEPT ![n] = newRcvd]
            /\ parent' = [parent EXCEPT ![n] = newPar]
            /\ inbox'  = [x \in Nodes |->
                            (IF x = n THEN inbox[x] \ {m} ELSE inbox[x])
                            \cup (IF x \in targets THEN {n} ELSE {})]

Done == rcvd[initiator] = Neighbors(initiator)

Terminated == Done /\ UNCHANGED vars

Next == (\E n \in Nodes : Receive(n)) \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(\E n \in Nodes : Receive(n))

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
ParentIsNeighbor ==
    \A n \in Nodes \ {initiator} :
        parent[n] # NoNode => <<n, parent[n]>> \in R

\* When the initiator is done, every node has a parent and no messages remain.
DoneCorrect ==
    Done => /\ \A n \in Nodes : parent[n] \in Nodes
            /\ \A n \in Nodes : inbox[n] = {}
            /\ \A n \in Nodes : rcvd[n] = Neighbors(n)

\* The parent pointers form a tree rooted at the initiator upon termination.
SpanningTree ==
    Done => \A n \in Nodes \ {initiator} :
               PathExists({<<x, parent[x]>> : x \in Nodes \ {initiator}},
                          Nodes, n, initiator)

Termination == <>Done

(***************************************************************************)
(* Test specification and TLC postcondition                                *)
(***************************************************************************)
TestSpec ==
    /\ PrintT(<<"R:", R>>)
    /\ Spec

\* Postcondition checked by TLC after model checking completes.
PostCondition ==
    /\ IsConnected(R, Nodes)
    /\ IsSymmetric(R, Nodes)
    /\ IsIrreflexive(R, Nodes)
    /\ TLCGet("stats").distinct > 0

=============================================================================