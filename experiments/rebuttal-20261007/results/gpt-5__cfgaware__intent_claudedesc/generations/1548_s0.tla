------------------------------ MODULE OneStepByzConsensus ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Faulty

ASSUME
  /\ N \in Nat /\ T \in Nat /\ F \in Nat
  /\ F <= T
  /\ N > 3*T
  /\ Faulty \subseteq 1..N
  /\ Cardinality(Faulty) <= F

(*
  Basic sets and helpers
*)
Proc == 1..N
Bits == {0, 1}
Correct == Proc \ Faulty
Thresh == N - T

VARIABLES
  val,     \* [Proc -> Bits], immutable input (initial proposals)
  dec,     \* [Proc -> {0,1,"U"}], decision state per process
  rc0,rc1, \* [Proc -> 0..N], counts of 0/1 received from correct senders
  rb0,rb1, \* [Proc -> 0..N], counts of 0/1 received from Byzantine senders
  sentC,   \* subset of Correct \X Proc: which (correct-sender,receiver) have delivered
  B0,B1    \* subsets of Faulty \X Proc: which (byz-sender,receiver) delivered value 0 / 1
          

vars == << val, dec, rc0, rc1, rb0, rb1, sentC, B0, B1 >>

DeliveredB == B0 \cup B1

Tot0(q) == rc0[q] + rb0[q]
Tot1(q) == rc1[q] + rb1[q]
Tot(q)  == Tot0(q) + Tot1(q)

DecideValue(q) ==
  IF Tot0(q) >= Thresh THEN 0
  ELSE IF Tot1(q) >= Thresh THEN 1
  ELSE val[q]

Init ==
  /\ val \in [Proc -> Bits]
  /\ dec = [p \in Proc |-> "U"]
  /\ rc0 = [p \in Proc |-> 0]
  /\ rc1 = [p \in Proc |-> 0]
  /\ rb0 = [p \in Proc |-> 0]
  /\ rb1 = [p \in Proc |-> 0]
  /\ sentC = {}
  /\ B0 = {}
  /\ B1 = {}

(*
  Delivery of a correct sender's single broadcast message to a receiver.
  Each correct sender p can deliver to each q at most once.
*)
DeliverFromCorrect(p, q) ==
  /\ p \in Correct /\ q \in Proc
  /\ <<p, q>> \notin sentC
  /\ sentC' = sentC \cup {<<p, q>>}
  /\ rc0' = [rc0 EXCEPT ![q] = rc0[q] + IF val[p] = 0 THEN 1 ELSE 0]
  /\ rc1' = [rc1 EXCEPT ![q] = rc1[q] + IF val[p] = 1 THEN 1 ELSE 0]
  /\ UNCHANGED << val, dec, rb0, rb1, B0, B1 >>

(*
  Byzantine sender can deliver at most one arbitrary bit to each receiver.
*)
DeliverFromByz0(p, q) ==
  /\ p \in Faulty /\ q \in Proc
  /\ <<p, q>> \notin DeliveredB
  /\ B0' = B0 \cup {<<p, q>>}
  /\ rb0' = [rb0 EXCEPT ![q] = rb0[q] + 1]
  /\ UNCHANGED << val, dec, rc0, rc1, sentC, B1, rb1 >>

DeliverFromByz1(p, q) ==
  /\ p \in Faulty /\ q \in Proc
  /\ <<p, q>> \notin DeliveredB
  /\ B1' = B1 \cup {<<p, q>>}
  /\ rb1' = [rb1 EXCEPT ![q] = rb1[q] + 1]
  /\ UNCHANGED << val, dec, rc0, rc1, sentC, B0, rb0 >>

(*
  Decision step for any process once it has received at least N-T messages.
*)
Decide(q) ==
  /\ q \in Proc
  /\ dec[q] = "U"
  /\ Tot(q) >= Thresh
  /\ dec' = [dec EXCEPT ![q] = DecideValue(q)]
  /\ UNCHANGED << val, rc0, rc1, rb0, rb1, sentC, B0, B1 >>

Next ==
  \E p \in Correct: \E q \in Proc: DeliverFromCorrect(p, q)
  \/ \E p \in Faulty: \E q \in Proc: DeliverFromByz0(p, q) \/ DeliverFromByz1(p, q)
  \/ \E q \in Proc: Decide(q)

Spec ==
  Init /\ [][Next]_vars
  /\ (\A p \in Correct: \A q \in Proc: WF_vars(DeliverFromCorrect(p, q)))
  /\ (\A q \in Proc: WF_vars(Decide(q)))

(*
  Type and basic safety invariants.
*)
TypeOK ==
  /\ Proc = 1..N
  /\ val \in [Proc -> Bits]
  /\ dec \in [Proc -> {0,1,"U"}]
  /\ rc0 \in [Proc -> 0..N]
  /\ rc1 \in [Proc -> 0..N]
  /\ rb0 \in [Proc -> 0..N]
  /\ rb1 \in [Proc -> 0..N]
  /\ sentC \subseteq (Correct \X Proc)
  /\ B0 \subseteq (Faulty \X Proc)
  /\ B1 \subseteq (Faulty \X Proc)
  /\ B0 \cap B1 = {}
  /\ \A q \in Proc:
        rc0[q] + rc1[q] <= Cardinality(Correct)
      /\ rb0[q] + rb1[q] <= Cardinality(Faulty)

(*
  LTL properties:
  - OneStep0_Ltl: If all correct processes propose 0 initially, then
      (i) no correct process ever decides 1, and
      (ii) eventually all correct processes decide 0.
  - OneStep1_Ltl: If all correct processes propose 1 initially, then
      (i) no correct process ever decides 0, and
      (ii) eventually all correct processes decide 1.
  - AllDecideOne: If all processes propose 1 initially, then eventually
      every process (including faulty ones) decides 1.
*)
OneStep0_Ltl ==
  (\A p \in Correct: val[p] = 0)
  => ( [](\A p \in Correct: dec[p] # 1)
       /\ <>(\A p \in Correct: dec[p] = 0)
     )

OneStep1_Ltl ==
  (\A p \in Correct: val[p] = 1)
  => ( [](\A p \in Correct: dec[p] # 0)
       /\ <>(\A p \in Correct: dec[p] = 1)
     )

AllDecideOne ==
  (\A p \in Proc: val[p] = 1)
  => <>(\A p \in Proc: dec[p] = 1)

=============================================================================