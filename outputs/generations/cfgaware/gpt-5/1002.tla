---- MODULE Barrier ----
EXTENDS Integers

CONSTANT N

VARIABLES pc

Proc == 1..N
PCStates == {"b0", "b1"}

TypeOK == pc \in [Proc -> PCStates]

Init == pc = [p \in Proc |-> "b0"]

Move(p) ==
  /\ p \in Proc
  /\ pc[p] = "b0"
  /\ pc' = [pc EXCEPT ![p] = "b1"]

BarrierReset ==
  /\ \A p \in Proc: pc[p] = "b1"
  /\ pc' = [q \in Proc |-> "b0"]

Next ==
  (\E p \in Proc: Move(p))
  \/ BarrierReset

Spec == Init /\ [][Next]_pc

BarrierProperty ==
  [] ( \A p \in Proc:
        (pc[p] = "b1" /\ pc'[p] = "b0")
          => (\A q \in Proc: pc[q] = "b1") )

====