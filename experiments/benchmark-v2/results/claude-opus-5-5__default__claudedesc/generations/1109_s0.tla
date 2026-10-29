------------------------------ MODULE SpanningTree ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Proc,      \* set of processes
          NoPrnt,    \* special value: no parent
          root,      \* the designated root process
          Nbrs       \* neighbor relation: a set of pairs <<p, q>>

ASSUME /\ NoPrnt \notin Proc
       /\ root \in Proc
       /\ Nbrs \subseteq Proc \X Proc
       /\ \A p, q \in Proc : (<<p, q>> \in Nbrs) => (<<q, p>> \in Nbrs)

VARIABLES parent,    \* parent[p] : the parent of process p, or NoPrnt
          reported,  \* reported[p] : TRUE iff p has reported its parent choice
          msgs       \* set of messages <<sender, receiver>> that have been sent

vars == <<parent, reported, msgs>>

Neighbors(p) == {q \in Proc : <<p, q>> \in Nbrs}

-----------------------------------------------------------------------------

Init == /\ parent   = [p \in Proc |-> NoPrnt]
        /\ reported = [p \in Proc |-> FALSE]
        /\ msgs     = {}

(* A process that is the root or already has a parent sends a message      *)
(* to one of its neighbors.                                                 *)
SendMsg(p) == /\ (p = root) \/ (parent[p] # NoPrnt)
              /\ \E q \in Neighbors(p) :
                    /\ <<p, q>> \notin msgs
                    /\ msgs' = msgs \cup {<<p, q>>}
              /\ UNCHANGED <<parent, reported>>

(* A non-root process without a parent receives a message from q and       *)
(* adopts q as its parent.                                                  *)
Receive(p) == /\ p # root
              /\ parent[p] = NoPrnt
              /\ \E q \in Proc :
                    /\ <<q, p>> \in msgs
                    /\ parent' = [parent EXCEPT ![p] = q]
              /\ UNCHANGED <<reported, msgs>>

(* After selecting a parent, a process reports its selection.               *)
Report(p) == /\ parent[p] # NoPrnt
             /\ ~reported[p]
             /\ reported' = [reported EXCEPT ![p] = TRUE]
             /\ UNCHANGED <<parent, msgs>>

Next == \E p \in Proc : SendMsg(p) \/ Receive(p) \/ Report(p)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------

TypeOK == /\ parent \in [Proc -> Proc \cup {NoPrnt}]
          /\ \A p \in Proc : parent[p] \in Neighbors(p) \cup {NoPrnt}
          /\ reported \in [Proc -> BOOLEAN]
          /\ msgs \subseteq Proc \X Proc
          /\ msgs \subseteq Nbrs

(* Processes without a parent (other than the root) have not sent messages *)
NoParentNoMsgs ==
    \A p \in Proc :
        (p # root /\ parent[p] = NoPrnt) => \A q \in Proc : <<p, q>> \notin msgs

(* Every non-root process eventually selects a valid parent.                *)
Termination ==
    <>(\A p \in Proc \ {root} : parent[p] \in Neighbors(p))

(* Once set, a parent assignment never changes.                             *)
Stability ==
    [][\A p \in Proc : parent[p] # NoPrnt => parent'[p] = parent[p]]_vars

StabilityTemporal ==
    \A p \in Proc, q \in Proc :
        [](parent[p] = q => [](parent[p] = q))

THEOREM Spec => [](TypeOK /\ NoParentNoMsgs)
THEOREM Spec => Stability
THEOREM Spec => Termination
=============================================================================