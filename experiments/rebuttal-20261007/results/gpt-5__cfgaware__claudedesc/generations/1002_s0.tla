----------------------------- MODULE CyclicBarrier -----------------------------
EXTENDS Integers

CONSTANT N

VARIABLES pc

Proc == 1..N
Loc  == {"b0", "b1"}

TypeOK == pc \in [Proc -> Loc]

Init == pc = [p \in Proc |-> "b0"]

b0(self) ==
  /\ self \in Proc
  /\ pc[self] = "b0"
  /\ pc' = [pc EXCEPT ![self] = "b1"]

b1 ==
  /\ \A p \in Proc: pc[p] = "b1"
  /\ pc' = [p \in Proc |-> "b0"]

Next ==
  \/ \E self \in Proc: b0(self)
  \/ b1

vars == << pc >>

Spec == Init /\ [][Next]_vars

BarrierProperty ==
  [] ( \A j \in Proc:
        ( (\E i \in Proc: pc[i] = "b0") /\ pc[j] = "b1" ) => pc'[j] = "b1" )

=============================================================================