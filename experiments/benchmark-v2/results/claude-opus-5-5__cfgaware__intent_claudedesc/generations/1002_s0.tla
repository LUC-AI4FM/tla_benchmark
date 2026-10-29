---------------------------- MODULE Barrier ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

VARIABLE pc

vars == << pc >>

Procs == 1..N

States == {"approaching", "waiting"}

TypeOK == pc \in [Procs -> States]

Init == pc = [p \in Procs |-> "approaching"]

Arrive(p) ==
    /\ pc[p] = "approaching"
    /\ pc' = [pc EXCEPT ![p] = "waiting"]

Release ==
    /\ \A p \in Procs : pc[p] = "waiting"
    /\ pc' = [p \in Procs |-> "approaching"]

Next == (\E p \in Procs : Arrive(p)) \/ Release

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

BarrierProperty ==
    [][\A p, q \in Procs :
          (pc[p] = "waiting" /\ pc'[p] = "approaching") => pc[q] = "waiting"]_vars

=============================================================================