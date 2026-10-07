------------------------------ MODULE OneStepConsensusByz ------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, F, T

(*
  N: number of processes
  F: maximum number of Byzantine faulty processes
  T: threshold for deciding a value
*)

CONSTANT Val
ASSUME Val = {0, 1}

Proc == 1..N
NoVal == "undef"

VARIABLES
  state,       \* [Proc -> {"init","sent","decided"}]
  prop,        \* [Proc -> Val], initial proposals
  decision,    \* [Proc -> Val \cup {NoVal}]
  inbox,       \* [Proc -> [Val -> Nat]], counts of received values per process
  delivered,   \* SUBSET (Proc \X Proc), delivered message edges as pairs <<s,r>>
  hasSent,     \* SUBSET Proc, processes that have broadcast
  faulty,      \* SUBSET Proc, set of Byzantine processes
  sent,        \* Nat, total number of messages sent (broadcasted edges accounted)
  rcvd         \* Nat, total number of messages received (delivered edges)

vars == << state, prop, decision, inbox, delivered, hasSent, faulty, sent, rcvd >>

ProcPairs == { <<s, r>> : s \in Proc, r \in Proc }

Correct == Proc \ faulty

CountReceived(p, v) == inbox[p][v]

All0Init == \A p \in Proc : prop[p] = 0
All1Init == \A p \in Proc : prop[p] = 1

Init ==
  /\ faulty = {}
  /\ hasSent = {}
  /\ delivered = {}
  /\ inbox = [p \in Proc |-> [v \in Val |-> 0]]
  /\ sent = 0
  /\ rcvd = 0
  /\ state = [p \in Proc |-> "init"]
  /\ decision = [p \in Proc |-> NoVal]
  /\ \E v \in Val : prop = [p \in Proc |-> v]

Send(p) ==
  /\ p \in Proc
  /\ p \notin hasSent
  /\ state[p] = "init"
  /\ hasSent' = hasSent \cup {p}
  /\ state' = [state EXCEPT ![p] = "sent"]
  /\ sent' = sent + N
  /\ UNCHANGED << faulty, delivered, inbox, rcvd, decision, prop >>

Deliver(s, r) ==
  \E v \in Val :
    /\ s \in hasSent
    /\ r \in Proc
    /\ <<s, r>> \notin delivered
    /\ (s \in faulty) \/ (v = prop[s])
    /\ delivered' = delivered \cup {<<s, r>>}
    /\ inbox' = [inbox EXCEPT ![r][v] = @ + 1]
    /\ rcvd' = rcvd + 1
    /\ UNCHANGED << faulty, hasSent, sent, state, decision, prop >>

Decide1(p) ==
  /\ p \in Proc
  /\ decision[p] = NoVal
  /\ CountReceived(p, 1) >= T
  /\ decision' = [decision EXCEPT ![p] = 1]
  /\ state' = [state EXCEPT ![p] = "decided"]
  /\ UNCHANGED << faulty, hasSent, delivered, inbox, rcvd, sent, prop >>

Decide0(p) ==
  /\ p \in Proc
  /\ decision[p] = NoVal
  /\ CountReceived(p, 0) >= T
  /\ decision' = [decision EXCEPT ![p] = 0]
  /\ state' = [state EXCEPT ![p] = "decided"]
  /\ UNCHANGED << faulty, hasSent, delivered, inbox, rcvd, sent, prop >>

BecomeFaulty(p) ==
  /\ p \in Proc
  /\ p \notin faulty
  /\ Cardinality(faulty) < F
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED << hasSent, delivered, inbox, rcvd, sent, state, decision, prop >>

SendAction == \E p \in Proc : Send(p)
DeliverAction == \E s \in Proc, r \in Proc : Deliver(s, r)
DecideAction == \E p \in Proc : Decide1(p) \/ Decide0(p)
FaultAction == \E p \in Proc : BecomeFaulty(p)

Main == SendAction \/ DeliverAction \/ DecideAction

Next == Main \/ FaultAction

Spec == Init /\ [][Next]_vars /\ WF_vars(Main)

(*
  Safety invariants
*)

TypeInv ==
  /\ faulty \subseteq Proc
  /\ hasSent \subseteq Proc
  /\ delivered \subseteq ProcPairs
  /\ \A pr \in delivered : pr \in { <<s,r>> : s \in hasSent, r \in Proc }
  /\ inbox \in [Proc -> [Val -> Nat]]
  /\ state \in [Proc -> {"init","sent","decided"}]
  /\ decision \in [Proc -> (Val \cup {NoVal})]
  /\ prop \in [Proc -> Val]
  /\ sent \in Nat
  /\ rcvd \in Nat

FaultBoundInv == Cardinality(faulty) <= F

AccountingInv ==
  /\ rcvd = Cardinality(delivered)
  /\ sent = N * Cardinality(hasSent)

IntegrityInv ==
  /\ \A p \in Proc :
       (decision[p] \in Val) => state[p] = "decided"

AgreementInv ==
  /\ \A p \in Correct :
       \A q \in Correct :
         (decision[p] \in Val /\ decision[q] \in Val) => decision[p] = decision[q]

ValiditySafety0 ==
  (All0Init) => (\A p \in Correct : decision[p] # 1)

ValiditySafety1 ==
  (All1Init) => (\A p \in Correct : decision[p] # 0)

Inv == TypeInv /\ FaultBoundInv /\ AccountingInv /\ IntegrityInv /\ AgreementInv

(*
  Liveness properties
*)

Termination ==
  <> (\A p \in Correct : decision[p] \in Val)

ValidityLiveness0 ==
  (All0Init) => <> (\A p \in Correct : decision[p] = 0)

ValidityLiveness1 ==
  (All1Init) => <> (\A p \in Correct : decision[p] = 1)

==============================