----------------------------- MODULE OneStepByzConsensus -----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, BYZ

Proc == 1..N
Correct == Proc \ BYZ

ASSUME
  /\ N \in Nat /\ N > 0
  /\ T \in Nat
  /\ F \in Nat
  /\ N > 3*T
  /\ T >= F
  /\ BYZ \subseteq Proc
  /\ Cardinality(BYZ) <= F

VARIABLES
  Prop,               \* proposals: [Proc -> {0,1}]
  Decision,           \* per-process decision state
  Recv0, Recv1,       \* per-process received counts for votes 0 and 1
  CorrectSent0, CorrectSent1, \* counts of votes sent by correct processes
  FaultySent0, FaultySent1    \* counts of votes sent by Byzantine processes (incl. forgeries)

DState == {"none","dec0","dec1","undec0","undec1"}

Sent0Total == CorrectSent0 + FaultySent0
Sent1Total == CorrectSent1 + FaultySent1

TotalRecv(p) == Recv0[p] + Recv1[p]

Init ==
  /\ Prop \in [Proc -> {0,1}]
  /\ Decision = [p \in Proc |-> "none"]
  /\ Recv0 = [p \in Proc |-> 0]
  /\ Recv1 = [p \in Proc |-> 0]
  /\ CorrectSent0 = Cardinality({p \in Correct : Prop[p] = 0})
  /\ CorrectSent1 = Cardinality({p \in Correct : Prop[p] = 1})
  /\ FaultySent0 = 0
  /\ FaultySent1 = 0

ByzSend0 ==
  /\ FaultySent0 < N
  /\ FaultySent0' = FaultySent0 + 1
  /\ UNCHANGED <<Prop, Decision, Recv0, Recv1, CorrectSent0, CorrectSent1, FaultySent1>>

ByzSend1 ==
  /\ FaultySent1 < N
  /\ FaultySent1' = FaultySent1 + 1
  /\ UNCHANGED <<Prop, Decision, Recv0, Recv1, CorrectSent0, CorrectSent1, FaultySent0>>

Receive0(p) ==
  /\ p \in Proc
  /\ Recv0[p] < Sent0Total
  /\ Recv0[p] + Recv1[p] < N
  /\ Recv0' = [Recv0 EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<Prop, Decision, Recv1, CorrectSent0, CorrectSent1, FaultySent0, FaultySent1>>

Receive1(p) ==
  /\ p \in Proc
  /\ Recv1[p] < Sent1Total
  /\ Recv0[p] + Recv1[p] < N
  /\ Recv1' = [Recv1 EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<Prop, Decision, Recv0, CorrectSent0, CorrectSent1, FaultySent0, FaultySent1>>

Receive(p) == Receive0(p) \/ Receive1(p)

DecideOrUndecide(p) ==
  /\ p \in Proc
  /\ Decision[p] = "none"
  /\ TotalRecv(p) >= N - T
  /\ Decision' =
       [Decision EXCEPT
         ![p] =
           IF Recv0[p] >= N - T THEN "dec0"
           ELSE IF Recv1[p] >= N - T THEN "dec1"
           ELSE IF Prop[p] = 0 THEN "undec0" ELSE "undec1"]
  /\ UNCHANGED <<Prop, Recv0, Recv1, CorrectSent0, CorrectSent1, FaultySent0, FaultySent1>>

Next ==
  \/ ByzSend0
  \/ ByzSend1
  \/ \E p \in Proc: Receive(p)
  \/ \E p \in Proc: DecideOrUndecide(p)

vars == <<Prop, Decision, Recv0, Recv1, CorrectSent0, CorrectSent1, FaultySent0, FaultySent1>>

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in (Proc \ BYZ): WF_vars(Receive(p))
  /\ \A p \in (Proc \ BYZ): WF_vars(DecideOrUndecide(p))

(*
 Safety invariants
*)
CountBounds ==
  /\ CorrectSent0 + CorrectSent1 = Cardinality(Correct)
  /\ CorrectSent0 \in 0..N
  /\ CorrectSent1 \in 0..N
  /\ FaultySent0 \in 0..N
  /\ FaultySent1 \in 0..N
  /\ \A p \in Proc:
       /\ Recv0[p] \in 0..N
       /\ Recv1[p] \in 0..N
       /\ Recv0[p] <= Sent0Total
       /\ Recv1[p] <= Sent1Total
       /\ Recv0[p] + Recv1[p] <= N

FaultBound == Cardinality(BYZ) <= F

AllCorrectZeroNoDecide1 ==
  (\A p \in Correct: Prop[p] = 0) => (\A p \in Correct: Decision[p] # "dec1")

AllCorrectOneNoDecide0 ==
  (\A p \in Correct: Prop[p] = 1) => (\A p \in Correct: Decision[p] # "dec0")

DecisionSound ==
  \A p \in Proc:
    /\ (Decision[p] = "dec0" => Recv0[p] >= N - T)
    /\ (Decision[p] = "dec1" => Recv1[p] >= N - T)
    /\ (Decision[p] \in {"undec0","undec1"} =>
          /\ Recv0[p] < N - T
          /\ Recv1[p] < N - T
          /\ TotalRecv(p) >= N - T)

SafetyInv == CountBounds /\ FaultBound /\ AllCorrectZeroNoDecide1 /\ AllCorrectOneNoDecide0 /\ DecisionSound

(*
 Liveness properties under weak fairness
*)
LivenessReceive == \A p \in Correct: WF_vars(Receive(p))
LivenessDecide  == \A p \in Correct: WF_vars(DecideOrUndecide(p))
Liveness == LivenessReceive /\ LivenessDecide

=============================================================================