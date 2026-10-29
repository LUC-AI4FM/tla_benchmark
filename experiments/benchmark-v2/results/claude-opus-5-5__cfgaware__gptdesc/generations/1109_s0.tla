---------------------------- MODULE SpanningTree ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, NoPrnt, root, nbrs

ASSUME /\ NoPrnt \notin Proc
       /\ root \in Proc
       /\ nbrs \subseteq Proc \X Proc

VARIABLES prnt, rpt, msg

vars == <<prnt, rpt, msg>>

TypeOK == /\ prnt \in [Proc -> Proc \cup {NoPrnt}]
          /\ rpt  \in [Proc -> BOOLEAN]
          /\ msg  \subseteq Proc \X Proc

Init == /\ prnt = [i \in Proc |-> NoPrnt]
        /\ rpt  = [i \in Proc |-> FALSE]
        /\ msg  = {}

CanSend(i, k) == /\ <<i, k>> \in nbrs
                 /\ \/ i = root
                    \/ prnt[i] # NoPrnt

Send(i, k) == /\ CanSend(i, k)
              /\ msg' = msg \cup {<<i, k>>}
              /\ UNCHANGED <<prnt, rpt>>

Update(i, k) == /\ i # root
                /\ prnt[i] = NoPrnt
                /\ <<k, i>> \in msg
                /\ prnt' = [prnt EXCEPT ![i] = k]
                /\ UNCHANGED <<rpt, msg>>

Next == \E i, k \in Proc : Send(i, k) \/ Update(i, k)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == \A i \in Proc \ {root} : <>(prnt[i] # NoPrnt)

PrntStable == \A i \in Proc :
                 [][prnt[i] # NoPrnt => prnt'[i] = prnt[i]]_prnt
=============================================================================