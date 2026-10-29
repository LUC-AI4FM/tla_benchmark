------------------------------ MODULE SpanTree ------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Proc, NoPrnt, root, nbrs

ASSUME /\ root \in Proc
       /\ NoPrnt \notin Proc
       /\ nbrs \subseteq Proc \X Proc

VARIABLES prnt, rpt, msg

vars == <<prnt, rpt, msg>>

InTree(i) == (i = root) \/ (prnt[i] # NoPrnt)

TypeOK ==
    /\ prnt \in [Proc -> Proc \cup {NoPrnt}]
    /\ rpt \in [Proc -> BOOLEAN]
    /\ msg \subseteq (Proc \X Proc)
    /\ \A i \in Proc : prnt[i] # NoPrnt => <<i, prnt[i]>> \in nbrs

Init ==
    /\ prnt = [i \in Proc |-> NoPrnt]
    /\ rpt = [i \in Proc |-> FALSE]
    /\ msg = {}

\* Process i, part of the tree, invites neighbor k to join
Send(i, k) ==
    /\ InTree(i)
    /\ ~rpt[i]
    /\ <<i, k>> \in nbrs
    /\ <<i, k>> \notin msg
    /\ msg' = msg \cup {<<i, k>>}
    /\ UNCHANGED <<prnt, rpt>>

\* Non-root process i without a parent adopts neighbor j as its parent
Update(i, j) ==
    /\ i # root
    /\ prnt[i] = NoPrnt
    /\ <<j, i>> \in msg
    /\ <<i, j>> \in nbrs
    /\ InTree(j)
    /\ prnt' = [prnt EXCEPT ![i] = j]
    /\ UNCHANGED <<rpt, msg>>

\* Process i reports that it has joined the tree (after inviting all neighbors)
Report(i) ==
    /\ InTree(i)
    /\ ~rpt[i]
    /\ \A k \in Proc : <<i, k>> \in nbrs => <<i, k>> \in msg
    /\ rpt' = [rpt EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<prnt, msg>>

Next ==
    \/ \E i, j \in Proc : Send(i, j) \/ Update(i, j)
    \/ \E i \in Proc : Report(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Correctness properties

MsgIntegrity == \A m \in msg : InTree(m[1])

Termination ==
    <>(\A i \in Proc \ {root} : prnt[i] \in Proc /\ <<i, prnt[i]>> \in nbrs)

Stability ==
    \A i \in Proc : [][prnt[i] # NoPrnt => prnt'[i] = prnt[i]]_vars

=============================================================================