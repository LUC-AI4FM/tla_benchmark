------------------------------ MODULE HuangTermination ------------------------------

EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS Proc, Leader, K

ASSUME Proc # {} /\ Leader \in Proc /\ K \in Nat

(*
  Discrete weight model:
  - Unit = 2^K total atomic weight units.
  - All weights are natural numbers in 0..Unit.
  - A send splits an even local weight exactly in half.
*)

RECURSIVE Pow2(_)
Pow2(n) == IF n = 0 THEN 1 ELSE 2 * Pow2(n - 1)

Unit == Pow2(K)

Kinds == {"fwd", "ret"}

Message == [to: Proc, wt: 0..Unit, kind: Kinds]

(*
  State variables:
    - active: set of currently active processes
    - w:      per-process local weight in 0..Unit
    - chan:   per-destination FIFO-like sequence of in-flight messages
*)
VARIABLES active, w, chan

Vars == << active, w, chan >>

IsEven(n) == \E k \in Nat: n = 2*k

RECURSIVE SumSet(_, _)
SumSet(S, f) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE e \in S: TRUE IN f[x] + SumSet(S \ {x}, f)

RECURSIVE SumSeq(_)
SumSeq(s) ==
  IF Len(s) = 0 THEN 0 ELSE Head(s).wt + SumSeq(Tail(s))

TotalProcWeight(w_) == SumSet(Proc, [p \in Proc |-> w_[p]])
TotalChanWeight(ch_) == SumSet(Proc, [p \in Proc |-> SumSeq(ch_[p])])

WeightSum(w_, ch_) == TotalProcWeight(w_) + TotalChanWeight(ch_)

RemoveAt(s, i) ==
  SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

MessagesOK(ch_) ==
  \A p \in Proc:
    \A i \in 1..Len(ch_[p]):
      /\ ch_[p][i] \in Message
      /\ ch_[p][i].to = p

TypeOK ==
  /\ active \subseteq Proc
  /\ w \in [Proc -> 0..Unit]
  /\ chan \in [Proc -> Seq(Message)]
  /\ MessagesOK(chan)
  /\ WeightSum(w, chan) = Unit

Init ==
  /\ active = {Leader}
  /\ w = [p \in Proc |-> IF p = Leader THEN Unit ELSE 0]
  /\ chan = [p \in Proc |-> << >>]
  /\ TypeOK

Send(p, q) ==
  /\ p \in Proc /\ q \in Proc /\ p # q
  /\ p \in active
  /\ IsEven(w[p]) /\ w[p] >= 2
  /\ LET half == w[p] \div 2 IN
       /\ w' = [w EXCEPT ![p] = @ \div 2]
       /\ chan' = [chan EXCEPT ![q] = Append(@, [to |-> q, wt |-> half, kind |-> "fwd"])]
  /\ active' = active

RecvFwd(q) ==
  /\ q \in Proc
  /\ \E i \in 1..Len(chan[q]):
       LET m == chan[q][i] IN
         /\ m.kind = "fwd"
         /\ m.to = q
         /\ w' = [w EXCEPT ![q] = @ + m.wt]
         /\ chan' = [chan EXCEPT ![q] = RemoveAt(@, i)]
         /\ active' = active \cup {q}

RecvReturn ==
  /\ \E i \in 1..Len(chan[Leader]):
       LET m == chan[Leader][i] IN
         /\ m.kind = "ret"
         /\ m.to = Leader
         /\ w' = [w EXCEPT ![Leader] = @ + m.wt]
         /\ chan' = [chan EXCEPT ![Leader] = RemoveAt(@, i)]
         /\ active' = active \cup {Leader}

IdleReturn(p) ==
  /\ p \in Proc \ {Leader}
  /\ p \in active
  /\ LET wt == w[p] IN
       /\ active' = active \ {p}
       /\ w' = [w EXCEPT ![p] = 0]
       /\ chan' = [chan EXCEPT ![Leader] = Append(@, [to |-> Leader, wt |-> wt, kind |-> "ret"])]

IdleLeader ==
  /\ Leader \in active
  /\ active' = active \ {Leader}
  /\ UNCHANGED << w, chan >>

Next ==
  \/ \E p \in Proc: \E q \in Proc: Send(p, q)
  \/ \E q \in Proc: RecvFwd(q)
  \/ RecvReturn
  \/ \E p \in Proc \ {Leader}: IdleReturn(p)
  \/ IdleLeader

Spec == Init /\ [][Next]_Vars

(*
  Predicates and properties
*)

TermDetected == (Leader \notin active) /\ (w[Leader] = Unit)

GenuineTerm ==
  /\ active = {}
  /\ \A p \in Proc: Len(chan[p]) = 0

Safety ==
  []( TermDetected => (GenuineTerm /\ [] TermDetected) )

Liveness ==
  (<>[] GenuineTerm) => (<> TermDetected)

=============================================================================