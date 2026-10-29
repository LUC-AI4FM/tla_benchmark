------------------------------ MODULE SpanningTree ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Proc,     \* the set of processes
          NoPrnt,   \* value meaning "no parent selected yet"
          root,     \* the distinguished root process
          nbrs      \* the neighbor relation, as a set of ordered pairs

\* The neighbor relation is the set of all symmetric pairs over Proc.
ASSUME /\ NoPrnt \notin Proc
       /\ root \in Proc
       /\ nbrs \subseteq Proc \X Proc
       /\ \A e \in nbrs : <<e[2], e[1]>> \in nbrs

Neighbors(p) == {q \in Proc : <<p, q>> \in nbrs}

\* The set of processes reachable from S through the neighbor relation.
RECURSIVE Closure(_)
Closure(S) ==
  LET T == S \cup {q \in Proc : \E p \in S : <<p, q>> \in nbrs}
  IN  IF T = S THEN S ELSE Closure(T)

\* The network is connected, so every process can reach the root.
ASSUME Closure({root}) = Proc

VARIABLES parent,    \* parent[p] is p's parent, or NoPrnt
          msgs,      \* set of messages <<from, to>> that have been sent
          reported   \* set of processes that have reported joining the tree

vars == <<parent, msgs, reported>>

\* A process is initiated when it is the root or has selected a parent.
Initiated(p) == (p = root) \/ (parent[p] # NoPrnt)

-----------------------------------------------------------------------------
Init == /\ parent = [p \in Proc |-> NoPrnt]
        /\ msgs = {}
        /\ reported = {}

\* An initiated process sends an invitation to one of its neighbors.
SendMsg(p) ==
  /\ Initiated(p)
  /\ \E q \in Neighbors(p) :
       /\ <<p, q>> \notin msgs
       /\ msgs' = msgs \cup {<<p, q>>}
  /\ UNCHANGED <<parent, reported>>

\* A non-root process without a parent adopts as parent some neighbor
\* that has sent it a message. That neighbor is necessarily initiated.
Adopt(p) ==
  /\ p # root
  /\ parent[p] = NoPrnt
  /\ \E q \in Neighbors(p) :
       /\ <<q, p>> \in msgs
       /\ Initiated(q)
       /\ parent' = [parent EXCEPT ![p] = q]
  /\ UNCHANGED <<msgs, reported>>

\* An initiated process reports that it has joined the tree.
Report(p) ==
  /\ Initiated(p)
  /\ p \notin reported
  /\ reported' = reported \cup {p}
  /\ UNCHANGED <<parent, msgs>>

Next == \E p \in Proc : SendMsg(p) \/ Adopt(p) \/ Report(p)

Fairness == \A p \in Proc : /\ WF_vars(SendMsg(p))
                            /\ WF_vars(Adopt(p))
                            /\ WF_vars(Report(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

\* Type safety: a parent must be a neighbor.
TypeOK ==
  /\ parent \in [Proc -> Proc \cup {NoPrnt}]
  /\ \A p \in Proc : parent[p] # NoPrnt => parent[p] \in Neighbors(p)
  /\ parent[root] = NoPrnt
  /\ msgs \subseteq nbrs
  /\ reported \subseteq Proc

\* Message integrity: only initiated processes send messages.
MsgIntegrity == \A m \in msgs : Initiated(m[1])

\* Only initiated processes report.
ReportIntegrity == \A p \in reported : Initiated(p)

Inv == TypeOK /\ MsgIntegrity /\ ReportIntegrity

\* Stability: once a parent is chosen, it never changes.
Stability ==
  \A p \in Proc :
    [][parent[p] # NoPrnt => parent'[p] = parent[p]]_parent

-----------------------------------------------------------------------------
\* Liveness properties

\* Termination: every non-root process eventually has a parent among its neighbors.
Termination ==
  <>(\A p \in Proc \ {root} : parent[p] \in Neighbors(p))

\* Every process eventually reports joining the tree.
AllReported == <>(reported = Proc)

THEOREM Spec => []Inv
THEOREM Spec => Stability
THEOREM Spec => Termination
=============================================================================