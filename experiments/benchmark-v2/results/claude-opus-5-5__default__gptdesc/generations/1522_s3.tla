------------------------------- MODULE Huang -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Procs, Leader, MaxExp

ASSUME /\ Leader \in Procs
       /\ IsFiniteSet(Procs)
       /\ MaxExp \in Nat

VARIABLES active, weight, msgs

vars == <<active, weight, msgs>>

(***************************************************************************)
(* Dyadic rationals: a weight is a record [num |-> n, exp |-> e]           *)
(* representing the value n / 2^e, kept in reduced form.                   *)
(***************************************************************************)
Pow2(e) == 2^e

RECURSIVE Reduce(_)
Reduce(x) == IF x.exp > 0 /\ x.num % 2 = 0
               THEN Reduce([num |-> x.num \div 2, exp |-> x.exp - 1])
               ELSE x

Zero == [num |-> 0, exp |-> 0]
One  == [num |-> 1, exp |-> 0]

Max(a, b) == IF a >= b THEN a ELSE b

Add(a, b) ==
  LET e == Max(a.exp, b.exp)
  IN Reduce([num |-> a.num * Pow2(e - a.exp) + b.num * Pow2(e - b.exp),
             exp |-> e])

Half(a) == Reduce([num |-> a.num, exp |-> a.exp + 1])

IsPositive(a) == a.num > 0

(***************************************************************************)
(* Messages are records [type |-> "work" or "ctrl", w |-> weight].         *)
(* msgs[p] is the FIFO queue of messages in transit to process p.          *)
(***************************************************************************)
Weights  == [num : Nat, exp : Nat]
Messages == [type : {"work", "ctrl"}, w : Weights]

RECURSIVE SumSeq(_)
SumSeq(s) == IF s = <<>> THEN Zero ELSE Add(Head(s).w, SumSeq(Tail(s)))

RECURSIVE SumSet(_, _)
SumSet(S, f(_)) == IF S = {} THEN Zero
                   ELSE LET p == CHOOSE x \in S : TRUE
                        IN Add(f(p), SumSet(S \ {p}, f))

ProcWeight(p) == Add(weight[p], SumSeq(msgs[p]))

TotalWeight == SumSet(Procs, ProcWeight)

-----------------------------------------------------------------------------

TypeOK ==
  /\ active \in [Procs -> BOOLEAN]
  /\ weight \in [Procs -> Weights]
  /\ msgs \in [Procs -> Seq(Messages)]

Init ==
  /\ active = [p \in Procs |-> p = Leader]
  /\ weight = [p \in Procs |-> IF p = Leader THEN One ELSE Zero]
  /\ msgs   = [p \in Procs |-> <<>>]

(* An active process sends a work message carrying half of its weight. *)
SendMsg(p) ==
  /\ active[p]
  /\ IsPositive(weight[p])
  /\ weight[p].exp < MaxExp
  /\ \E q \in Procs \ {p} :
        /\ weight' = [weight EXCEPT ![p] = Half(weight[p])]
        /\ msgs' = [msgs EXCEPT ![q] =
                      Append(@, [type |-> "work", w |-> Half(weight[p])])]
  /\ UNCHANGED active

(* A process receives the message at the head of its queue. *)
RcvMsg(p) ==
  /\ msgs[p] /= <<>>
  /\ LET m == Head(msgs[p])
     IN /\ weight' = [weight EXCEPT ![p] = Add(@, m.w)]
        /\ msgs' = [msgs EXCEPT ![p] = Tail(@)]
        /\ active' = IF m.type = "work"
                       THEN [active EXCEPT ![p] = TRUE]
                       ELSE active

(* An active process becomes idle; a non-leader returns its weight to the leader. *)
Idle(p) ==
  /\ active[p]
  /\ active' = [active EXCEPT ![p] = FALSE]
  /\ IF p = Leader
       THEN UNCHANGED <<weight, msgs>>
       ELSE /\ weight' = [weight EXCEPT ![p] = Zero]
            /\ msgs' = [msgs EXCEPT ![Leader] =
                          Append(@, [type |-> "ctrl", w |-> weight[p]])]

Next == \E p \in Procs : SendMsg(p) \/ RcvMsg(p) \/ Idle(p)

Fairness == \A p \in Procs : WF_vars(Idle(p)) /\ WF_vars(RcvMsg(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

TerminationDetected == ~active[Leader] /\ weight[Leader] = One

(* Sum of all process weights and weights in transit is always 1. *)
WeightInvariant == TotalWeight = One

(* Idle non-leader processes hold no weight. *)
IdleNoWeight == \A p \in Procs \ {Leader} : ~active[p] => weight[p] = Zero

(* Once termination is detected, all processes are idle and no messages remain. *)
Safety ==
  TerminationDetected =>
     \A p \in Procs : ~active[p] /\ msgs[p] = <<>>

(* Termination is eventually detected. *)
Liveness == <>TerminationDetected

(* Once detected, termination is stable. *)
StableTermination == [](TerminationDetected => []TerminationDetected)

=============================================================================