---------------------------- MODULE barrier ----------------------------

EXTENDS Naturals

CONSTANT N

VARIABLES pc, arrived

vars == <<pc, arrived>>

Procs == 1..N

States == {"approaching", "atBarrier"}

TypeOK == /\ pc \in [Procs -> States]
          /\ arrived \subseteq Procs

Init == /\ pc = [p \in Procs |-> "approaching"]
        /\ arrived = {}

Arrive(p) == /\ pc[p] = "approaching"
             /\ pc' = [pc EXCEPT ![p] = "atBarrier"]
             /\ arrived' = arrived \cup {p}

Release == /\ arrived = Procs
           /\ pc' = [p \in Procs |-> "approaching"]
           /\ arrived' = {}

Next == \/ \E p \in Procs : Arrive(p)
        \/ Release

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

SomeNotArrived == \E q \in Procs : pc[q] = "approaching"

SomeAtBarrier == \E p \in Procs : pc[p] = "atBarrier"

BarrierProperty == [][~(SomeAtBarrier /\ SomeNotArrived) => 
                      (\A p \in Procs : pc[p] = "atBarrier" => pc'[p] # "approaching")]_vars

=========================================================================