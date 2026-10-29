------------------------------- MODULE SpanningTree -------------------------------
(***************************************************************************)
(* Distributed spanning-tree construction over a fixed, undirected,        *)
(* connected network.                                                      *)
(*                                                                         *)
(* Messages are modeled abstractly as "explore" tokens <<from, to>>        *)
(* travelling along network links. Channels are reliable: messages are     *)
(* never lost and never duplicated. They are delivered asynchronously and  *)
(* in any order.                                                           *)
(*                                                                         *)
(* A process decides on its parent using only its own local state and the  *)
(* message it receives from a neighbor.                                    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc,       \* the finite set of processes
    Root,       \* the designated root process
    Edge,       \* the set of links, as pairs <<p, q>>; treated as undirected
    Nil         \* the value meaning "no parent"

ASSUME RootInProc   == Root \in Proc
ASSUME NilNotProc   == Nil \notin Proc
ASSUME EdgeWF       == Edge \subseteq (Proc \X Proc)
ASSUME FiniteProc   == IsFiniteSet(Proc)

\* Undirected neighbor relation (no self-loops).
Nbrs(p) == { q \in Proc \ {p} : <<p, q>> \in Edge \/ <<q, p>> \in Edge }

\* The set of processes reachable from S in the network graph.
RECURSIVE Reach(_)
Reach(S) == LET T == S \cup UNION { Nbrs(q) : q \in S }
            IN  IF T = S THEN S ELSE Reach(T)

\* The network is connected, so a spanning tree exists.
ASSUME Connected == Reach({Root}) = Proc

N == Cardinality(Proc)

\* The set of all possible messages: explore tokens sent along links.
Msg == { [from |-> p, to |-> q] : p \in Proc, q \in Proc }

VARIABLES
    parent,     \* parent[p] \in Proc \cup {Nil}
    msgs,       \* the set of messages currently in transit
    sent        \* sent[p] = TRUE iff p has already sent explore to its neighbors

vars == <<parent, msgs, sent>>

----------------------------------------------------------------------------------
\* The n-th ancestor of p, or Nil if the chain of parents ends before that.
RECURSIVE Up(_, _)
Up(p, n) == IF n = 0 THEN p
            ELSE IF p = Nil THEN Nil
            ELSE IF parent[p] = Nil THEN Nil
            ELSE Up(parent[p], n - 1)

\* Following parent pointers from p eventually reaches the Root.
ReachesRoot(p) == \E n \in 0..N : Up(p, n) = Root

----------------------------------------------------------------------------------
TypeOK ==
    /\ parent \in [Proc -> Proc \cup {Nil}]
    /\ msgs \subseteq Msg
    /\ sent \in [Proc -> BOOLEAN]

Init ==
    /\ parent = [p \in Proc |-> Nil]     \* the root and every other process start with no parent
    /\ msgs = {}
    /\ sent = [p \in Proc |-> FALSE]

(* Process p sends explore messages to all of its neighbors. It does this  *)
(* once: the root may send immediately, and any other process may send     *)
(* once it has adopted a parent.                                           *)
Broadcast(p) ==
    /\ ~sent[p]
    /\ (p = Root \/ parent[p] # Nil)
    /\ sent' = [sent EXCEPT ![p] = TRUE]
    /\ msgs' = msgs \cup { [from |-> p, to |-> q] : q \in Nbrs(p) }
    /\ UNCHANGED parent

(* Delivering message m. The receiver adopts the sender as its parent if   *)
(* the receiver is not the root and has no parent yet. Otherwise the       *)
(* message is simply consumed.                                             *)
Receive(m) ==
    /\ m \in msgs
    /\ msgs' = msgs \ {m}
    /\ parent' = IF m.to # Root /\ parent[m.to] = Nil
                    THEN [parent EXCEPT ![m.to] = m.from]
                    ELSE parent
    /\ UNCHANGED sent

\* The protocol has finished: no messages are in transit and every process has broadcast.
Terminated ==
    /\ msgs = {}
    /\ \A p \in Proc : sent[p]

Done == Terminated /\ UNCHANGED vars     \* stuttering after termination (avoids deadlock)

Next ==
    \/ \E p \in Proc : Broadcast(p)
    \/ \E m \in Msg  : Receive(m)
    \/ Done

Fairness ==
    /\ \A p \in Proc : WF_vars(Broadcast(p))
    /\ \A m \in Msg  : WF_vars(Receive(m))

Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------------
(*************************** Safety properties ****************************)

\* Every parent pointer is always a neighbor.
ParentIsNeighbor ==
    \A p \in Proc : parent[p] # Nil => parent[p] \in Nbrs(p)

\* The root never has a parent.
RootHasNoParent == parent[Root] = Nil

\* Parent pointers never form a cycle.
NoCycle ==
    \A p \in Proc : ~(\E n \in 1..N : Up(p, n) = p)

\* Stronger invariant: every process that has a parent has an ancestor chain leading to the root.
RootedForest ==
    \A p \in Proc : parent[p] # Nil => ReachesRoot(p)

\* Messages only travel along network links.
MsgsOnLinks ==
    \A m \in msgs : m.to \in Nbrs(m.from)

\* The spanning-tree property.
SpanningTree ==
    /\ parent[Root] = Nil
    /\ \A p \in Proc \ {Root} : parent[p] \in Nbrs(p)
    /\ \A p \in Proc : ReachesRoot(p)
    /\ NoCycle

\* Once stabilized, the parent relation is a spanning tree rooted at Root.
StableImpliesTree == Terminated => SpanningTree

Safety ==
    /\ TypeOK
    /\ ParentIsNeighbor
    /\ RootHasNoParent
    /\ NoCycle
    /\ RootedForest
    /\ MsgsOnLinks
    /\ StableImpliesTree

\* Once a process has a parent, that parent never changes.
ParentStable ==
    [][\A p \in Proc : parent[p] # Nil => parent'[p] = parent[p]]_vars

\* A configuration that is a spanning tree remains one, and its parent pointers stay the same.
TreePersists ==
    [](SpanningTree => [][UNCHANGED parent]_vars)

(************************** Liveness properties ***************************)

\* Eventually the system stabilizes for good.
EventuallyTerminated == <>[]Terminated

\* The system eventually converges to a spanning tree and stays there.
Convergence == <>[]SpanningTree

\* Eventually, parent pointers stop changing.
EventuallyNoParentChange == <>[][UNCHANGED parent]_vars

\* Messages eventually quiesce: no infinite message generation.
MessageQuiescence == <>[](msgs = {})

\* From any reachable state, the system eventually reaches stability with a spanning tree.
LeadsToStable == TRUE ~> (Terminated /\ SpanningTree)

Liveness ==
    /\ EventuallyTerminated
    /\ Convergence
    /\ EventuallyNoParentChange
    /\ MessageQuiescence
    /\ LeadsToStable

----------------------------------------------------------------------------------
THEOREM Spec => []Safety
THEOREM Spec => ParentStable /\ TreePersists
THEOREM Spec => Liveness
==================================================================================