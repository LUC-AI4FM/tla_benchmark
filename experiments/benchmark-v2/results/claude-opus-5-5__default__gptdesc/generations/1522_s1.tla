------------------------------- MODULE Huang -------------------------------
(***************************************************************************)
(* Huang's weight-throwing distributed termination detection algorithm.    *)
(* Weights are dyadic rationals. Each weight w is stored as the natural     *)
(* number w * Total, where Total = 2^MaxSends. At most MaxSends basic       *)
(* messages are sent, so every halving gives an exact integer, and the     *)
(* integer Total stands for the rational weight 1.                         *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Procs, Leader, MaxSends

ASSUME /\ Leader \in Procs
       /\ MaxSends \in Nat

RECURSIVE Pow2(_)
Pow2(n) == IF n = 0 THEN 1 ELSE 2 * Pow2(n - 1)

Total == Pow2(MaxSends)   \* represents the dyadic rational 1

VARIABLES active,   \* active[p] : is process p active?
          weight,   \* weight[p] : weight held by p (scaled by Total)
          msgs,     \* msgs[p]   : queue of messages in transit to p
          sent      \* number of basic messages sent so far

vars == <<active, weight, msgs, sent>>

Msg == [type : {"basic", "control"}, w : 0..Total]

TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ weight \in [Procs -> 0..Total]
    /\ msgs \in [Procs -> Seq(Msg)]
    /\ sent \in 0..MaxSends

-----------------------------------------------------------------------------
(* Summation helpers *)
RECURSIVE SumSeq(_)
SumSeq(s) == IF s = <<>> THEN 0 ELSE Head(s).w + SumSeq(Tail(s))

RECURSIVE SumSet(_, _)
SumSet(f, S) == IF S = {} THEN 0
                ELSE LET x == CHOOSE y \in S : TRUE
                     IN  f[x] + SumSet(f, S \ {x})

InTransit == [p \in Procs |-> SumSeq(msgs[p])]

TotalWeight == SumSet(weight, Procs) + SumSet(InTransit, Procs)

-----------------------------------------------------------------------------
Init ==
    /\ active = [p \in Procs |-> p = Leader]
    /\ weight = [p \in Procs |-> IF p = Leader THEN Total ELSE 0]
    /\ msgs   = [p \in Procs |-> <<>>]
    /\ sent   = 0

(* An active process sends a basic message carrying half its weight. *)
SendMsg(p, q) ==
    /\ active[p]
    /\ sent < MaxSends
    /\ weight[p] > 1
    /\ weight[p] % 2 = 0
    /\ q # p
    /\ weight' = [weight EXCEPT ![p] = @ \div 2]
    /\ msgs'   = [msgs EXCEPT ![q] = Append(@, [type |-> "basic",
                                               w    |-> weight[p] \div 2])]
    /\ sent'   = sent + 1
    /\ UNCHANGED active

(* A process receives a message: basic messages activate it; control *)
(* messages (only sent to the leader) merely return weight.         *)
RcvMsg(p) ==
    /\ msgs[p] # <<>>
    /\ LET m == Head(msgs[p]) IN
         /\ weight' = [weight EXCEPT ![p] = @ + m.w]
         /\ active' = IF m.type = "basic"
                        THEN [active EXCEPT ![p] = TRUE]
                        ELSE active
    /\ msgs' = [msgs EXCEPT ![p] = Tail(@)]
    /\ UNCHANGED sent

(* An active process becomes idle. A non-leader returns its weight to *)
(* the leader in a control message; the leader keeps its weight.      *)
Idle(p) ==
    /\ active[p]
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ IF p = Leader
         THEN UNCHANGED <<weight, msgs>>
         ELSE /\ weight' = [weight EXCEPT ![p] = 0]
              /\ msgs'   = [msgs EXCEPT ![Leader] =
                              Append(@, [type |-> "control", w |-> weight[p]])]
    /\ UNCHANGED sent

TerminationDetected ==
    /\ ~active[Leader]
    /\ weight[Leader] = Total

(* Stuttering once termination is detected, to avoid deadlock. *)
Done ==
    /\ TerminationDetected
    /\ UNCHANGED vars

Next ==
    \/ \E p, q \in Procs : SendMsg(p, q)
    \/ \E p \in Procs : RcvMsg(p)
    \/ \E p \in Procs : Idle(p)
    \/ Done

Fairness ==
    /\ \A p \in Procs : WF_vars(RcvMsg(p))
    /\ \A p \in Procs : WF_vars(Idle(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety *)

\* The sum of all process weights and weights in transit is always 1.
WeightInvariant == TotalWeight = Total

\* Every active process holds a positive weight.
ActiveHasWeight == \A p \in Procs : active[p] => weight[p] > 0

\* Termination is detected only if all processes are idle and no
\* messages are in transit.
Safety ==
    TerminationDetected =>
        /\ \A p \in Procs : ~active[p]
        /\ \A p \in Procs : msgs[p] = <<>>

(* Liveness *)

Terminated ==
    /\ \A p \in Procs : ~active[p]
    /\ \A p \in Procs : msgs[p] = <<>>

Liveness == <>TerminationDetected

TerminationLeadsToDetection == Terminated ~> TerminationDetected

StableDetection == [](TerminationDetected => []TerminationDetected)

THEOREM Spec => [](TypeOK /\ WeightInvariant /\ ActiveHasWeight /\ Safety)
THEOREM Spec => Liveness /\ TerminationLeadsToDetection
=============================================================================