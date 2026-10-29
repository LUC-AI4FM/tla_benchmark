------------------------------ MODULE Huang ------------------------------
EXTENDS Naturals, FiniteSets, Bags, TLC

CONSTANTS L, P1, P2, P3, Leader, Procs

ASSUME Leader \in Procs

VARIABLES active, weight, msgs, terminated

vars == <<active, weight, msgs, terminated>>

-----------------------------------------------------------------------------
(* Exact rational weights with power-of-two denominators.                 *)

MaxDen == 8

Max(a, b) == IF a >= b THEN a ELSE b

Frac == [num : Nat, den : Nat]

RECURSIVE Norm(_)
Norm(f) == IF f.den > 1 /\ f.num % 2 = 0
             THEN Norm([num |-> f.num \div 2, den |-> f.den \div 2])
             ELSE f

Zero == [num |-> 0, den |-> 1]
One  == [num |-> 1, den |-> 1]

Add(a, b) == LET m == Max(a.den, b.den)
             IN Norm([num |-> a.num * (m \div a.den) + b.num * (m \div b.den),
                      den |-> m])

Half(a) == Norm([num |-> a.num, den |-> a.den * 2])

Scale(n, f) == Norm([num |-> n * f.num, den |-> f.den])

IsZero(a) == a.num = 0

RECURSIVE SumProcs(_)
SumProcs(S) == IF S = {} THEN Zero
               ELSE LET p == CHOOSE x \in S : TRUE
                    IN Add(weight[p], SumProcs(S \ {p}))

RECURSIVE SumMsgs(_)
SumMsgs(S) == IF S = {} THEN Zero
              ELSE LET m == CHOOSE x \in S : TRUE
                   IN Add(Scale(CopiesIn(m, msgs), m.w), SumMsgs(S \ {m}))

TotalWeight == Add(SumProcs(Procs), SumMsgs(BagToSet(msgs)))

Msg == [type : {"work", "ack"}, to : Procs, w : Frac]

-----------------------------------------------------------------------------

TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ weight \in [Procs -> Frac]
    /\ \A p \in Procs : weight[p].den > 0
    /\ IsABag(msgs)
    /\ \A m \in BagToSet(msgs) : m \in Msg /\ m.w.den > 0
    /\ terminated \in BOOLEAN

Init ==
    /\ active = [p \in Procs |-> p = Leader]
    /\ weight = [p \in Procs |-> IF p = Leader THEN One ELSE Zero]
    /\ msgs = EmptyBag
    /\ terminated = FALSE

(* An active process does work by sending half its weight in a work msg. *)
SendWork(p, q) ==
    /\ active[p]
    /\ q # p
    /\ ~IsZero(weight[p])
    /\ LET h == Half(weight[p])
       IN /\ weight' = [weight EXCEPT ![p] = h]
          /\ msgs' = msgs (+) SetToBag({[type |-> "work", to |-> q, w |-> h]})
    /\ UNCHANGED <<active, terminated>>

(* Receipt of a work message (arbitrary order): activates and adds weight. *)
RecvWork(m) ==
    /\ m.type = "work"
    /\ active' = [active EXCEPT ![m.to] = TRUE]
    /\ weight' = [weight EXCEPT ![m.to] = Add(weight[m.to], m.w)]
    /\ msgs' = msgs (-) SetToBag({m})
    /\ UNCHANGED terminated

(* Leader receives returned weight. *)
RecvAck(m) ==
    /\ m.type = "ack"
    /\ weight' = [weight EXCEPT ![Leader] = Add(weight[Leader], m.w)]
    /\ msgs' = msgs (-) SetToBag({m})
    /\ UNCHANGED <<active, terminated>>

Receive ==
    \E m \in BagToSet(msgs) : RecvWork(m) \/ RecvAck(m)

(* Non-leader becomes idle and returns its weight to the leader. *)
BecomeIdle(p) ==
    /\ p # Leader
    /\ active[p]
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ weight' = [weight EXCEPT ![p] = Zero]
    /\ msgs' = msgs (+) SetToBag({[type |-> "ack", to |-> Leader, w |-> weight[p]]})
    /\ UNCHANGED terminated

(* Leader becomes idle, keeping its weight and waiting for returns. *)
LeaderIdle ==
    /\ active[Leader]
    /\ active' = [active EXCEPT ![Leader] = FALSE]
    /\ UNCHANGED <<weight, msgs, terminated>>

Detect ==
    /\ ~terminated
    /\ ~active[Leader]
    /\ weight[Leader] = One
    /\ terminated' = TRUE
    /\ UNCHANGED <<active, weight, msgs>>

Next ==
    \/ \E p, q \in Procs : SendWork(p, q)
    \/ Receive
    \/ \E p \in Procs : BecomeIdle(p)
    \/ LeaderIdle
    \/ Detect

Spec == Init /\ [][Next]_vars /\ WF_vars(Detect) /\ WF_vars(Receive)

-----------------------------------------------------------------------------

WeightConservation == TotalWeight = One

Quiescent == (\A p \in Procs : ~active[p]) /\ BagToSet(msgs) = {}

Safe == terminated => Quiescent

Live == [](Quiescent => <>terminated)

StateConstraint ==
    /\ \A p \in Procs : weight[p].den <= MaxDen
    /\ \A m \in BagToSet(msgs) : m.w.den <= MaxDen

Alias ==
    [active     |-> active,
     weight     |-> weight,
     msgs       |-> msgs,
     terminated |-> terminated,
     total      |-> TotalWeight]

=============================================================================