----------------------------- MODULE Barrier -----------------------------
EXTENDS Naturals, TLC

CONSTANT N

VARIABLES pc

Proc == 1..N
States == {"pre", "arrived"}

Init ==
  pc = [p \in Proc |-> "pre"]

AllArrived ==
  \A p \in Proc: pc[p] = "arrived"

Arrive(p) ==
  /\ p \in Proc
  /\ pc[p] = "pre"
  /\ pc' = [pc EXCEPT ![p] = "arrived"]

Release ==
  /\ AllArrived
  /\ pc' = [p \in Proc |-> "pre"]

Next ==
  ( \E p \in Proc: Arrive(p) ) \/ Release

Spec ==
  Init /\ [][Next]_pc

TypeOK ==
  pc \in [Proc -> States]

BarrierProperty ==
  [] ( \A p \in Proc:
        (pc[p] = "arrived" /\ pc'[p] = "pre") => AllArrived )

============================================================================