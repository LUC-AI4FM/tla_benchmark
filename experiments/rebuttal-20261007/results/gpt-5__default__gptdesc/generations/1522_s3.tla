------------------------------ MODULE HuangTermination ------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Procs, Leader, PRECISION

ASSUME /\ Procs # {}
       /\ Leader \in Procs
       /\ PRECISION \in Nat

Unit == 2 ^ PRECISION

Message == [from: Procs, w: Nat]

VARIABLES active, weight, inbox, terminated

vars == << active, weight, inbox, terminated >>

Init ==
  /\ active = [p \in Procs |-> p = Leader]
  /\ weight = [p \in Procs |-> IF p = Leader THEN Unit ELSE 0]
  /\ inbox  = [p \in Procs |-> << >>]
  /\ terminated = FALSE

RECURSIVE SumSeq(_)
SumSeq(s) ==
  IF Len(s) = 0
  THEN 0
  ELSE s[1].w + SumSeq(Tail(s))

RECURSIVE SumSet(_,_)
SumSet(F, S) ==
  IF S = {}
  THEN 0
  ELSE
    LET x == CHOOSE y \in S: TRUE
    IN F[x] + SumSet(F, S \ {x})

ProcWeightSum == SumSet([p \in Procs |-> weight[p]], Procs)
TransitWeightSum == SumSet([p \in Procs |-> SumSeq(inbox[p])], Procs)

AllIdle  == \A p \in Procs: ~active[p]
AllEmpty == \A p \in Procs: Len(inbox[p]) = 0

TotalWeightIsUnit == ProcWeightSum + TransitWeightSum = Unit

Send(p, q) ==
  /\ ~terminated
  /\ p \in Procs /\ q \in Procs /\ p # q
  /\ active[p]
  /\ weight[p] >= 2
  /\ LET ws  == weight[p] \div 2
         msg == [from |-> p, w |-> ws]
     IN
       /\ weight' = [weight EXCEPT ![p] = @ - ws]
       /\ inbox'  = [inbox  EXCEPT ![q] = Append(@, msg)]
       /\ UNCHANGED << active, terminated >>

Receive(q) ==
  /\ ~terminated
  /\ q \in Procs
  /\ Len(inbox[q]) > 0
  /\ LET m == Head(inbox[q])
     IN
       /\ inbox'  = [inbox  EXCEPT ![q] = Tail(@)]
       /\ weight' = [weight EXCEPT ![q] = @ + m.w]
       /\ active' = [active EXCEPT ![q] = TRUE]
       /\ UNCHANGED terminated

Deactivate(p) ==
  /\ ~terminated
  /\ p \in Procs
  /\ active[p]
  /\ active' = [active EXCEPT ![p] = FALSE]
  /\ UNCHANGED << weight, inbox, terminated >>

Return(p) ==
  /\ ~terminated
  /\ p \in Procs
  /\ p # Leader
  /\ ~active[p]
  /\ weight[p] > 0
  /\ LET msg == [from |-> p, w |-> weight[p]]
     IN
       /\ inbox'  = [inbox  EXCEPT ![Leader] = Append(@, msg)]
       /\ weight' = [weight EXCEPT ![p] = 0]
       /\ UNCHANGED << active, terminated >>

Detect ==
  /\ ~terminated
  /\ ~active[Leader]
  /\ AllEmpty
  /\ weight[Leader] = Unit
  /\ terminated' = TRUE
  /\ UNCHANGED << active, weight, inbox >>

Next ==
  \/ \E p \in Procs, q \in Procs: Send(p, q)
  \/ \E q \in Procs: Receive(q)
  \/ \E p \in Procs: Deactivate(p)
  \/ \E p \in Procs \ {Leader}: Return(p)
  \/ Detect

Fairness ==
  /\ \A q \in Procs: WF_vars(Receive(q))
  /\ \A p \in Procs \ {Leader}: WF_vars(Return(p))
  /\ WF_vars(Detect)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Fairness

SafetyWeights ==
  []TotalWeightIsUnit

SafetyTermination ==
  [](terminated => AllIdle /\ AllEmpty
                    /\ weight[Leader] = Unit
                    /\ \A p \in Procs \ {Leader}: weight[p] = 0)

LivenessTermination ==
  <>terminated

=============================================================================