---------------------------- MODULE BarrierSync ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N
VARIABLES processes, round, released

Process == 1..N
Phase == {"arrived", "released"}

Init ==
  /\ processes \in [Process -> Phase]
  /\ round \in Nat
  /\ released = FALSE
  /\ processes = [p \in Process |-> "arrived"]

Next ==
  \/ \E p \in Process :
      /\ processes[p] = "arrived"
      /\ processes' = [processes EXCEPT ![p] = "released"]
      /\ round' = round
      /\ released' = (released \/ (\A q \in Process : processes[q] = "arrived"))
  \/ \E p \in Process :
      /\ processes[p] = "released"
      /\ processes' = [processes EXCEPT ![p] = "arrived"]
      /\ round' = round
      /\ released' = FALSE
  \/ (released /\ \A q \in Process : processes[q] = "released")
      /\ processes' = [p \in Process |-> "arrived"]
      /\ round' = round + 1
      /\ released' = FALSE

Spec == Init /\ [][Next]_<<processes, round, released>>
TypeOK == 
  /\ processes \in [Process -> Phase]
  /\ round \in Nat
  /\ released \in BOOLEAN
BarrierProperty == Spec => []TypeOK /\ WF_vars(Next, <<processes, round, released>>)

THEOREM Spec => BarrierProperty
=============================================================================