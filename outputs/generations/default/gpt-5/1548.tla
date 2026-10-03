------------------------------ MODULE OneStepByzConsensus ------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, F, T

ASSUME
  /\ N \in Nat /\ N >= 1
  /\ F \in Nat /\ F < N
  /\ T \in Nat /\ T >= 1 /\ T <= N

(*
  Processes, values, and a distinguished "no decision" value.
*)
Proc   == 1..N
Values == {0, 1}
NoVal  == -1

VARIABLES
  Proposals,     \* [Proc -> Values], fixed after Init
  Faulty,        \* SUBSET Proc, size bounded by F
  State,         \* [Proc -> {"start","sent","recv","done","faulty"}]
  Sent,          \* [Proc -> BOOLEAN], has process performed the propose/send step
  NSent0,        \* Nat, number of processes that executed Propose with value 0
  NSent1,        \* Nat, number of processes that executed Propose with value 1
  Delivered,     \* SUBSET (Proc \X Proc), set of delivered (sender,receiver) pairs
  Recv0,         \* [Proc -> Nat], count of 0-messages received by each process
  Recv1,         \* [Proc -> Nat], count of 1-messages received by each process
  Decided,       \* [Proc -> (Values \cup {NoVal})]
  ReceivedMsgs   \* Nat, total number of delivered messages (cardinality of Delivered)
  

vars == << Proposals, Faulty, State, Sent, NSent0, NSent1, Delivered, Recv0, Recv1, Decided, ReceivedMsgs >>

All0 == \A p \in Proc: Proposals[p] = 0
All1 == \A p \in Proc: Proposals[p] = 1

TypeOK ==
  /\ Proposals \in [Proc -> Values]
  /\ Faulty \subseteq Proc
  /\ State \in [Proc -> {"start","sent","recv","done","faulty"}]
  /\ Sent \in [Proc -> BOOLEAN]
  /\ NSent0 \in Nat /\ NSent1 \in Nat
  /\ Delivered \subseteq (Proc \X Proc)
  /\ Recv0 \in [Proc -> Nat] /\ Recv1 \in [Proc -> Nat]
  /\ Decided \in [Proc -> (Values \cup {NoVal})]
  /\ ReceivedMsgs \in Nat

Init ==
  /\ Proposals \in [Proc -> Values]
  /\ (All0 \/ All1)
  /\ Faulty = {}
  /\ State = [p \in Proc |-> "start"]
  /\ Sent  = [p \in Proc |-> FALSE]
  /\ NSent0 = 0 /\ NSent1 = 0
  /\ Delivered = {}
  /\ Recv0 = [p \in Proc |-> 0]
  /\ Recv1 = [p \in Proc |-> 0]
  /\ Decided = [p \in Proc |-> NoVal]
  /\ ReceivedMsgs = 0

(*
  A correct process executes its one-step broadcast ("propose").
*)
Propose(p) ==
  /\ p \in Proc
  /\ p \notin Faulty
  /\ ~Sent[p]
  /\ Proposals' = Proposals
  /\ Faulty'    = Faulty
  /\ Sent'      = [Sent EXCEPT ![p] = TRUE]
  /\ NSent0'    = NSent0 + IF Proposals[p] = 0 THEN 1 ELSE 0
  /\ NSent1'    = NSent1 + IF Proposals[p] = 1 THEN 1 ELSE 0
  /\ Delivered' = Delivered
  /\ Recv0'     = Recv0
  /\ Recv1'     = Recv1
  /\ Decided'   = Decided
  /\ ReceivedMsgs' = ReceivedMsgs
  /\ State'     = [State EXCEPT ![p] = "sent"]

(*
  Delivery of a message from q to p. A correct sender q can only have its proposal
  value delivered and only after it has executed Propose. A faulty sender may send
  any value at any time (even if it never executed Propose).
*)
Receive(p, q, v) ==
  /\ p \in Proc /\ q \in Proc
  /\ (Sent[q] \/ q \in Faulty)
  /\ ~(<<q, p>> \in Delivered)
  /\ v \in Values
  /\ (q \in Faulty) \/ (v = Proposals[q])
  /\ Proposals' = Proposals
  /\ Faulty'    = Faulty
  /\ Sent'      = Sent
  /\ NSent0'    = NSent0
  /\ NSent1'    = NSent1
  /\ Delivered' = Delivered \cup {<<q, p>>}
  /\ Recv0'     = [Recv0 EXCEPT ![p] = @ + IF v = 0 THEN 1 ELSE 0]
  /\ Recv1'     = [Recv1 EXCEPT ![p] = @ + IF v = 1 THEN 1 ELSE 0]
  /\ Decided'   = Decided
  /\ ReceivedMsgs' = ReceivedMsgs + 1
  /\ State'     = [State EXCEPT ![p] = "recv"]

(*
  Decision by a correct process: decide v if it has received at least T messages of v.
*)
Decide(p) ==
  /\ p \in Proc
  /\ p \notin Faulty
  /\ Decided[p] = NoVal
  /\ \E v \in Values:
       /\ IF v = 0 THEN Recv0[p] >= T ELSE Recv1[p] >= T
       /\ Proposals' = Proposals
       /\ Faulty'    = Faulty
       /\ Sent'      = Sent
       /\ NSent0'    = NSent0
       /\ NSent1'    = NSent1
       /\ Delivered' = Delivered
       /\ Recv0'     = Recv0
       /\ Recv1'     = Recv1
       /\ Decided'   = [Decided EXCEPT ![p] = v]
       /\ ReceivedMsgs' = ReceivedMsgs
       /\ State'     = [State EXCEPT ![p] = "done"]

(*
  A process may become Byzantine faulty, up to F processes in total.
*)
BecomeFaulty(p) ==
  /\ p \in Proc
  /\ p \notin Faulty
  /\ Cardinality(Faulty) < F
  /\ Proposals' = Proposals
  /\ Faulty'    = Faulty \cup {p}
  /\ Sent'      = Sent
  /\ NSent0'    = NSent0
  /\ NSent1'    = NSent1
  /\ Delivered' = Delivered
  /\ Recv0'     = Recv0
  /\ Recv1'     = Recv1
  /\ Decided'   = Decided
  /\ ReceivedMsgs' = ReceivedMsgs
  /\ State'     = [State EXCEPT ![p] = "faulty"]

(*
  The main protocol step includes proposing, receiving, and deciding.
  Fault transitions are modeled separately to allow fairness on protocol progress.
*)
MainStep ==
  \/ \E p \in Proc: Propose(p)
  \/ \E p \in Proc, q \in Proc, v \in Values: Receive(p, q, v)
  \/ \E p \in Proc: Decide(p)

Next ==
  MainStep
  \/ \E p \in Proc: BecomeFaulty(p)

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(MainStep)

(***************************************************************************)
(*                          Safety invariants                              *)
(***************************************************************************)

InvBounds ==
  Cardinality(Faulty) <= F

InvCounters ==
  /\ ReceivedMsgs = Cardinality(Delivered)
  /\ NSent0 + NSent1 = Cardinality({ p \in Proc: Sent[p] })

InvAgreement ==
  \A p, q \in Proc:
    (p \notin Faulty /\ q \notin Faulty /\ Decided[p] \in Values /\ Decided[q] \in Values)
      => Decided[p] = Decided[q]

InvValidity0 ==
  (All0) => (\A p \in Proc: Decided[p] \in {0, NoVal})

InvValidity1 ==
  (All1) => (\A p \in Proc: Decided[p] \in {1, NoVal})

InvDecisionJustified ==
  \A p \in Proc:
    /\ (Decided[p] = 0 => Recv0[p] >= T)
    /\ (Decided[p] = 1 => Recv1[p] >= T)

TypeInvariant == TypeOK

Safety == TypeOK /\ InvBounds /\ InvCounters /\ InvAgreement /\ InvValidity0 /\ InvValidity1 /\ InvDecisionJustified

(***************************************************************************)
(*                           Liveness properties                           *)
(***************************************************************************)

Termination ==
  <> (\A p \in Proc: p \notin Faulty => Decided[p] \in Values)

=============================================================================