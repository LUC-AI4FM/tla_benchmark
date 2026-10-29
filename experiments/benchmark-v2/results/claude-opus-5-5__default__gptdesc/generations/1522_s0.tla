------------------------------- MODULE Huang -------------------------------
(***************************************************************************)
(* Huang's termination detection algorithm (Wikipedia version).           *)
(* Weights are dyadic rationals, represented as records [num, den] where  *)
(* den is a power of two and the fraction is kept in lowest terms.        *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Procs, Leader

ASSUME LeaderInProcs == Leader \in Procs
ASSUME ProcsFinite == IsFiniteSet(Procs)

VARIABLES active,   \* active[p] : is process p active?
          weight,   \* weight[p] : dyadic rational weight held by p
          msgs      \* msgs[p]   : sequence of messages in transit to p

vars == << active, weight, msgs >>

---------------------------------------------------------------------------
(* Dyadic rational arithmetic                                              *)

Zero == [num |-> 0, den |-> 1]
One  == [num |-> 1, den |-> 1]

RECURSIVE Reduce(_)
Reduce(r) ==
    IF r.num = 0 THEN Zero
    ELSE IF r.num % 2 = 0 /\ r.den % 2 = 0
         THEN Reduce([num |-> r.num \div 2, den |-> r.den \div 2])
         ELSE r

Add(a, b) == Reduce([num |-> a.num * b.den + b.num * a.den,
                     den |-> a.den * b.den])

Half(a) == Reduce([num |-> a.num, den |-> 2 * a.den])

IsPositive(a) == a.num > 0

RECURSIVE IsPow2(_)
IsPow2(n) == IF n = 1 THEN TRUE
             ELSE IF n > 1 /\ n % 2 = 0 THEN IsPow2(n \div 2)
             ELSE FALSE

IsDyadic(a) == /\ a \in [num : Nat, den : Nat \ {0}]
               /\ IsPow2(a.den)

---------------------------------------------------------------------------
(* Messages                                                                *)

BasicMsg(w) == [type |-> "basic", w |-> w]   \* computation message
CtrlMsg(w)  == [type |-> "ctrl",  w |-> w]   \* weight returned to Leader

RECURSIVE SumSeq(_)
SumSeq(s) == IF s = << >> THEN Zero
             ELSE Add(Head(s).w, SumSeq(Tail(s)))

RECURSIVE SumAll(_)
SumAll(S) ==
    IF S = {} THEN Zero
    ELSE LET p == CHOOSE x \in S : TRUE
         IN  Add(Add(weight[p], SumSeq(msgs[p])), SumAll(S \ {p}))

---------------------------------------------------------------------------

TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ \A p \in Procs : IsDyadic(weight[p])
    /\ \A p \in Procs : \A i \in 1..Len(msgs[p]) :
          /\ msgs[p][i].type \in {"basic", "ctrl"}
          /\ IsDyadic(msgs[p][i].w)

Init ==
    /\ active = [p \in Procs |-> p = Leader]
    /\ weight = [p \in Procs |-> IF p = Leader THEN One ELSE Zero]
    /\ msgs   = [p \in Procs |-> << >>]

(* An active process sends a basic message to q, carrying half its weight *)
SendMsg(p, q) ==
    /\ active[p]
    /\ q # p
    /\ weight' = [weight EXCEPT ![p] = Half(weight[p])]
    /\ msgs'   = [msgs EXCEPT ![q] = Append(@, BasicMsg(Half(weight[p])))]
    /\ UNCHANGED active

(* A process receives the message at the head of its queue                *)
RcvMsg(p) ==
    /\ msgs[p] # << >>
    /\ LET m == Head(msgs[p])
       IN  /\ weight' = [weight EXCEPT ![p] = Add(@, m.w)]
           /\ msgs'   = [msgs EXCEPT ![p] = Tail(@)]
           /\ active' = IF m.type = "basic"
                          THEN [active EXCEPT ![p] = TRUE]
                          ELSE active

(* A non-leader process becomes idle and returns its weight to the Leader *)
Idle(p) ==
    /\ p # Leader
    /\ active[p]
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ weight' = [weight EXCEPT ![p] = Zero]
    /\ msgs'   = [msgs EXCEPT ![Leader] = Append(@, CtrlMsg(weight[p]))]

(* The Leader becomes idle, keeping its weight                            *)
IdleLeader ==
    /\ active[Leader]
    /\ active' = [active EXCEPT ![Leader] = FALSE]
    /\ UNCHANGED << weight, msgs >>

Next ==
    \/ \E p, q \in Procs : SendMsg(p, q)
    \/ \E p \in Procs : RcvMsg(p)
    \/ \E p \in Procs : Idle(p)
    \/ IdleLeader

Fairness ==
    /\ \A p \in Procs : WF_vars(RcvMsg(p))
    /\ \A p \in Procs : WF_vars(Idle(p))
    /\ WF_vars(IdleLeader)

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Properties                                                              *)

TerminationDetected ==
    /\ ~active[Leader]
    /\ weight[Leader] = One

Terminated ==
    /\ \A p \in Procs : ~active[p]
    /\ \A p \in Procs : \A i \in 1..Len(msgs[p]) : msgs[p][i].type # "basic"

(* Sum of all weights held and in transit is always 1 *)
WeightInvariant == SumAll(Procs) = One

(* Active processes and messages always carry positive weight *)
PositiveWeights ==
    /\ \A p \in Procs : active[p] => IsPositive(weight[p])
    /\ \A p \in Procs : \A i \in 1..Len(msgs[p]) : IsPositive(msgs[p][i].w)

(* Safety: when termination is detected, every process is idle and all *)
(* messages have been delivered.                                        *)
Safety ==
    TerminationDetected =>
        /\ \A p \in Procs : ~active[p]
        /\ \A p \in Procs : msgs[p] = << >>

(* Liveness: once the computation has terminated, termination is        *)
(* eventually detected.                                                  *)
Liveness == Terminated ~> TerminationDetected

(* Once detected, termination stays detected *)
StableDetection == [](TerminationDetected => []TerminationDetected)

THEOREM Spec => [](TypeOK /\ WeightInvariant /\ PositiveWeights /\ Safety)
THEOREM Spec => Liveness
=============================================================================