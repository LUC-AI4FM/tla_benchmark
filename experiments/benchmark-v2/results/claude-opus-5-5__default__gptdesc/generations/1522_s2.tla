------------------------------- MODULE Huang -------------------------------
(***************************************************************************)
(* Huang's weight-throwing distributed termination detection algorithm.    *)
(*                                                                         *)
(* A set of processes Procs contains a distinguished Leader (the           *)
(* controlling agent). Each process has an active flag and a weight. Each  *)
(* process also has an incoming FIFO queue of messages in transit.         *)
(*                                                                         *)
(*  - Initially only the Leader is active and it holds weight 1.           *)
(*  - An active process may send a work message to another process. It     *)
(*    halves its weight and attaches one half to the message.              *)
(*  - On receiving a work message, a process becomes active and adds the   *)
(*    weight of the message to its own weight.                             *)
(*  - When a non-leader process becomes idle, it sends its whole weight    *)
(*    back to the Leader in a control message.                             *)
(*  - The Leader adds the weight of each control message to its own        *)
(*    weight. Termination is detected when the Leader is idle and holds    *)
(*    weight 1.                                                            *)
(*                                                                         *)
(* Weights are dyadic rationals num / den, with den a power of 2. They are *)
(* represented explicitly as records in canonical (reduced) form.          *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Procs, Leader

ASSUME LeaderInProcs == Leader \in Procs
ASSUME ProcsFinite   == IsFiniteSet(Procs)

VARIABLES active,   \* active[p] : BOOLEAN
          weight,   \* weight[p] : dyadic rational held by p
          msgs      \* msgs[p]   : sequence of messages in transit to p

vars == <<active, weight, msgs>>

---------------------------------------------------------------------------
(***************************************************************************)
(* Dyadic rational arithmetic                                              *)
(***************************************************************************)
Max(a, b) == IF a >= b THEN a ELSE b

RECURSIVE IsPow2(_)
IsPow2(n) == IF n = 1 THEN TRUE
             ELSE IF n = 0 \/ n % 2 = 1 THEN FALSE
             ELSE IsPow2(n \div 2)

RECURSIVE Reduce(_)
Reduce(r) == IF r.num % 2 = 0 /\ r.den > 1
               THEN Reduce([num |-> r.num \div 2, den |-> r.den \div 2])
               ELSE IF r.num = 0 THEN [num |-> 0, den |-> 1]
               ELSE r

Zero == [num |-> 0, den |-> 1]
One  == [num |-> 1, den |-> 1]

Add(r, s) ==
  LET d == Max(r.den, s.den)
  IN  Reduce([num |-> r.num * (d \div r.den) + s.num * (d \div s.den),
              den |-> d])

Half(r) == Reduce([num |-> r.num, den |-> 2 * r.den])

IsPositive(r) == r.num > 0

IsDyadic(r) == /\ r \in [num : Nat, den : Nat \ {0}]
               /\ IsPow2(r.den)

---------------------------------------------------------------------------
(***************************************************************************)
(* Messages                                                                *)
(***************************************************************************)
WorkMsg(w) == [type |-> "work", w |-> w]
CtrlMsg(w) == [type |-> "ctrl", w |-> w]

---------------------------------------------------------------------------
TypeOK ==
  /\ active \in [Procs -> BOOLEAN]
  /\ \A p \in Procs : IsDyadic(weight[p])
  /\ \A p \in Procs : 
        \A i \in 1..Len(msgs[p]) :
           /\ msgs[p][i].type \in {"work", "ctrl"}
           /\ IsDyadic(msgs[p][i].w)

---------------------------------------------------------------------------
Init ==
  /\ active = [p \in Procs |-> p = Leader]
  /\ weight = [p \in Procs |-> IF p = Leader THEN One ELSE Zero]
  /\ msgs   = [p \in Procs |-> << >>]

(***************************************************************************)
(* An active process p sends a work message to q carrying half its weight. *)
(***************************************************************************)
SendMsg(p, q) ==
  /\ active[p]
  /\ q # p
  /\ weight' = [weight EXCEPT ![p] = Half(weight[p])]
  /\ msgs'   = [msgs EXCEPT ![q] = Append(@, WorkMsg(Half(weight[p])))]
  /\ UNCHANGED active

(***************************************************************************)
(* Process p receives the message at the head of its queue.                *)
(***************************************************************************)
RcvMsg(p) ==
  /\ msgs[p] # << >>
  /\ LET m == Head(msgs[p]) IN
       /\ weight' = [weight EXCEPT ![p] = Add(@, m.w)]
       /\ msgs'   = [msgs EXCEPT ![p] = Tail(@)]
       /\ active' = IF m.type = "work"
                      THEN [active EXCEPT ![p] = TRUE]
                      ELSE active

(***************************************************************************)
(* Active process p becomes idle. A non-leader returns its weight to the   *)
(* Leader in a control message. The Leader simply keeps its weight.        *)
(***************************************************************************)
Idle(p) ==
  /\ active[p]
  /\ active' = [active EXCEPT ![p] = FALSE]
  /\ IF p = Leader
       THEN UNCHANGED <<weight, msgs>>
       ELSE /\ weight' = [weight EXCEPT ![p] = Zero]
            /\ msgs'   = [msgs EXCEPT ![Leader] =
                                 Append(@, CtrlMsg(weight[p]))]

Next ==
  \E p \in Procs :
     \/ \E q \in Procs : SendMsg(p, q)
     \/ RcvMsg(p)
     \/ Idle(p)

Fairness ==
  \A p \in Procs : /\ WF_vars(RcvMsg(p))
                   /\ WF_vars(Idle(p))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
RECURSIVE SumMsgs(_)
SumMsgs(s) == IF s = << >> THEN Zero ELSE Add(Head(s).w, SumMsgs(Tail(s)))

RECURSIVE SumProcs(_)
SumProcs(S) ==
  IF S = {} THEN Zero
  ELSE LET p == CHOOSE x \in S : TRUE
       IN  Add(Add(weight[p], SumMsgs(msgs[p])), SumProcs(S \ {p}))

\* The sum of all process weights and the weights of all messages in transit is 1.
WeightInvariant == SumProcs(Procs) = One

\* Every active process and every message in transit carries a positive weight.
PositiveWeights ==
  /\ \A p \in Procs : active[p] => IsPositive(weight[p])
  /\ \A p \in Procs : \A i \in 1..Len(msgs[p]) : IsPositive(msgs[p][i].w)

\* Control messages are only sent to the Leader.
CtrlOnlyToLeader ==
  \A p \in Procs \ {Leader} :
     \A i \in 1..Len(msgs[p]) : msgs[p][i].type = "work"

\* The computation has actually terminated.
Terminated ==
  /\ \A p \in Procs : ~active[p]
  /\ \A p \in Procs : \A i \in 1..Len(msgs[p]) : msgs[p][i].type # "work"

\* The Leader has detected termination.
TerminationDetected ==
  /\ ~active[Leader]
  /\ weight[Leader] = One

\* Safety: if termination is detected, all processes are idle and all
\* messages have been delivered.
Safety ==
  TerminationDetected =>
     /\ \A p \in Procs : ~active[p]
     /\ \A p \in Procs : msgs[p] = << >>

\* Liveness: termination is eventually detected once it has occurred.
Liveness == Terminated ~> TerminationDetected

\* Once termination is detected, it stays detected.
StableDetection == [](TerminationDetected => []TerminationDetected)

THEOREM Spec => [](TypeOK /\ WeightInvariant /\ PositiveWeights
                   /\ CtrlOnlyToLeader /\ Safety)
THEOREM Spec => Liveness
=============================================================================