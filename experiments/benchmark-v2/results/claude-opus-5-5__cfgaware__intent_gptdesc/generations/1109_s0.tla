---------------------------- MODULE SpanningTree ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, NoPrnt, root, nbrs

ASSUME /\ NoPrnt \notin Proc
       /\ root \in Proc
       /\ nbrs \subseteq Proc \X Proc
       /\ \A e \in nbrs : <<e[2], e[1]>> \in nbrs

VARIABLES prnt, rpt, msg

vars == <<prnt, rpt, msg>>

TypeOK ==
  /\ prnt \in [Proc -> Proc \cup {NoPrnt}]
  /\ rpt \in [Proc -> BOOLEAN]
  /\ msg \subseteq Proc \X Proc

Init ==
  /\ prnt = [i \in Proc |-> NoPrnt]
  /\ rpt = [i \in Proc |-> FALSE]
  /\ msg = {}

CanSend(i, k) ==
  /\ <<i, k>> \in nbrs
  /\ \/ i = root
     \/ prnt[i] # NoPrnt

Send(i, k) ==
  /\ CanSend(i, k)
  /\ msg' = msg \cup {<<i, k>>}
  /\ UNCHANGED <<prnt, rpt>>

Update(i, j) ==
  /\ i # root
  /\ prnt[i] = NoPrnt
  /\ <<j, i>> \in msg
  /\ prnt' = [prnt EXCEPT ![i] = j]
  /\ UNCHANGED <<rpt, msg>>

Parent(i) ==
  /\ prnt[i] # NoPrnt
  /\ ~rpt[i]
  /\ rpt' = [rpt EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<prnt, msg>>

Terminated ==
  /\ \A i \in Proc \ {root} : prnt[i] # NoPrnt
  /\ UNCHANGED vars

Next ==
  \/ \E i, k \in Proc : Send(i, k)
  \/ \E i, j \in Proc : Update(i, j)
  \/ \E i \in Proc : Parent(i)
  \/ Terminated

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i, k \in Proc : WF_vars(Send(i, k))
  /\ \A i, j \in Proc : WF_vars(Update(i, j))
  /\ \A i \in Proc : WF_vars(Parent(i))

-----------------------------------------------------------------------------
\* Safety properties

PrntOK ==
  \A i \in Proc : \/ prnt[i] = NoPrnt
                  \/ <<i, prnt[i]>> \in nbrs

PrntStable ==
  [][\A i \in Proc : prnt[i] # NoPrnt => prnt'[i] = prnt[i]]_vars

OnlyParentedSend ==
  \A m \in msg : \/ m[1] = root
                 \/ prnt[m[1]] # NoPrnt

Safety == TypeOK /\ PrntOK /\ OnlyParentedSend

\* Liveness property

AllParented ==
  \A i \in Proc \ {root} : <>(prnt[i] # NoPrnt /\ <<i, prnt[i]>> \in nbrs)

Termination ==
  <>(\A i \in Proc \ {root} : prnt[i] # NoPrnt /\ <<i, prnt[i]>> \in nbrs)

=============================================================================