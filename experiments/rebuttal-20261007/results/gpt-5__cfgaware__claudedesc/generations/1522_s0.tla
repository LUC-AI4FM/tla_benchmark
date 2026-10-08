------------------------------ MODULE HuangTermination ------------------------------

EXTENDS Naturals, Sequences, TLC

CONSTANTS
  Procs,    \* Nonempty finite set of processes
  Leader,   \* Distinguished leader in Procs
  MaxExp    \* Maximum allowed denominator exponent (state-space bound)

VARIABLES
  Active,   \* [Procs -> BOOLEAN], activity flag per process
  W,        \* [Procs -> Dyad], weight per process
  Q         \* [Procs -> Seq(Dyad)], incoming message queue per process

vars == << Active, W, Q >>

\* Dyadic rational represented as record [num: Nat, exp: Nat] meaning num / 2^exp
IsDyad(r) ==
  /\ r \in [num: Nat, exp: Nat]
  /\ r.num <= 2 ^ r.exp

Zero == [num |-> 0, exp |-> 0]
One  == [num |-> 1, exp |-> 0]

IsZero(r) == r.num = 0

CommonExp(a, b) == IF a.exp >= b.exp THEN a.exp ELSE b.exp

DyEqual(a, b) ==
  LET e == CommonExp(a, b)
  IN a.num * (2 ^ (e - a.exp)) = b.num * (2 ^ (e - b.exp))

ToExp(r, e) == [num |-> r.num * (2 ^ (e - r.exp)), exp |-> e]

Add(a, b) ==
  LET e == CommonExp(a, b)
  IN [num |-> a.num * (2 ^ (e - a.exp)) + b.num * (2 ^ (e - b.exp)), exp |-> e]

Half(r) == [num |-> r.num, exp |-> r.exp + 1]

RECURSIVE SumSeq(_)
SumSeq(s) == IF Len(s) = 0 THEN 0 ELSE Head(s) + SumSeq(Tail(s))

RECURSIVE SumSet(_,_)
SumSet(S, f) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S: TRUE
       IN f[x] + SumSet(S \ {x}, f)

NumAtMax(r) == ToExp(r, MaxExp).num

ProcNumFunc == [p \in Procs |-> NumAtMax(W[p])]
ProcTotal   == SumSet(Procs, ProcNumFunc)

MsgNumsOf(p) == [i \in 1..Len(Q[p]) |-> NumAtMax(Q[p][i])]
MsgTotal     == SumSet(Procs, [p \in Procs |-> SumSeq(MsgNumsOf(p))])

TotalNum == ProcTotal + MsgTotal

TypeOK ==
  /\ Leader \in Procs
  /\ Procs # {}
  /\ Active \in [Procs -> BOOLEAN]
  /\ W \in [Procs -> [num: Nat, exp: Nat]]
  /\ \A p \in Procs: IsDyad(W[p])
  /\ Q \in [Procs -> Seq([num: Nat, exp: Nat])]
  /\ \A p \in Procs: \A i \in 1..Len(Q[p]): IsDyad(Q[p][i])
  /\ \A p \in Procs: W[p].exp <= MaxExp
  /\ \A p \in Procs: \A i \in 1..Len(Q[p]): Q[p][i].exp <= MaxExp
  /\ TotalNum = 2 ^ MaxExp

StateConstraint ==
  /\ \A p \in Procs: W[p].exp <= MaxExp
  /\ \A p \in Procs: \A i \in 1..Len(Q[p]): Q[p][i].exp <= MaxExp

Init ==
  /\ Active = [p \in Procs |-> p = Leader]
  /\ W = [p \in Procs |-> IF p = Leader THEN One ELSE Zero]
  /\ Q = [p \in Procs |-> <<>>]

Send(p, q) ==
  /\ p \in Procs /\ q \in Procs /\ q # p
  /\ Active[p]
  /\ ~IsZero(W[p])
  /\ LET h == Half(W[p]) IN
     /\ W' = [W EXCEPT ![p] = h]
     /\ Q' = [Q EXCEPT ![q] = Append(@, h)]
     /\ Active' = Active

Rcv(p) ==
  /\ p \in Procs \ {Leader}
  /\ Len(Q[p]) > 0
  /\ LET m == Head(Q[p]) IN
     /\ Q' = [Q EXCEPT ![p] = Tail(@)]
     /\ W' = [W EXCEPT ![p] = Add(@, m)]
     /\ Active' = [Active EXCEPT ![p] = TRUE]

RcvLdr ==
  /\ Len(Q[Leader]) > 0
  /\ LET m == Head(Q[Leader]) IN
     /\ Q' = [Q EXCEPT ![Leader] = Tail(@)]
     /\ W' = [W EXCEPT ![Leader] = Add(@, m)]
     /\ Active' = Active

Idle(p) ==
  /\ p \in Procs \ {Leader}
  /\ Active[p]
  /\ LET msg == W[p] IN
     /\ W' = [W EXCEPT ![p] = Zero]
     /\ Q' = [Q EXCEPT ![Leader] = Append(@, msg)]
     /\ Active' = [Active EXCEPT ![p] = FALSE]

IdleLdr ==
  /\ Active[Leader]
  /\ Active' = [Active EXCEPT ![Leader] = FALSE]
  /\ UNCHANGED << W, Q >>

Next ==
  \E p \in Procs: \E q \in Procs \ {p}: Send(p, q)
  \/ \E p \in Procs \ {Leader}: Rcv(p)
  \/ RcvLdr
  \/ \E p \in Procs \ {Leader}: Idle(p)
  \/ IdleLdr

DetectTerm ==
  /\ ~Active[Leader]
  /\ DyEqual(W[Leader], One)

Terminated ==
  /\ \A p \in Procs: ~Active[p]
  /\ \A p \in Procs: Q[p] = <<>>
  /\ DyEqual(W[Leader], One)
  /\ \A p \in Procs \ {Leader}: IsZero(W[p])

Fair ==
  /\ WF_vars(RcvLdr)
  /\ WF_vars(IdleLdr)
  /\ \A p \in Procs \ {Leader}: WF_vars(Rcv(p))
  /\ \A p \in Procs \ {Leader}: WF_vars(Idle(p))

Spec == Init /\ [][Next]_vars /\ Fair

Safe == [] (DetectTerm => [] Terminated)
Live == <> DetectTerm

THEOREM Spec => Safe
THEOREM Spec => Live

=============================================================================