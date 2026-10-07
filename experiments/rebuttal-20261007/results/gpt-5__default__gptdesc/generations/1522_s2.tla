------------------------------ MODULE HuangTermination ------------------------------

EXTENDS Naturals, Sequences

CONSTANTS Procs, Leader

ASSUME Leader \in Procs

VARIABLES
  active,    \* [Procs -> BOOLEAN]
  weight,    \* [Procs -> Real] (conceptually; we use numeric division by 2)
  chan,      \* [Procs -> Seq(Messages)] where Messages are records [src, dst, w]
  detected   \* BOOLEAN

vars == << active, weight, chan, detected >>

\* Sum of weights over a sequence of messages (by their 'w' field).
RECURSIVE SeqSum(_)
SeqSum(s) ==
  IF Len(s) = 0 THEN 0
  ELSE s[1].w + SeqSum(Tail(s))

\* Sum of f[x] over a finite set S, by structural recursion.
RECURSIVE SetSum(_, _)
SetSum(S, f) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE y \in S: TRUE IN
      f[x] + SetSum(S \ {x}, f)

AllChannelsEmpty == \A p \in Procs: Len(chan[p]) = 0
AllIdle          == \A p \in Procs: ~active[p]

TotalProcWeight == SetSum(Procs, weight)
TotalMsgWeight  == SetSum(Procs, [p \in Procs |-> SeqSum(chan[p])])

SumInvariant == TotalProcWeight + TotalMsgWeight = 1

ProcWeightsNonNeg == \A p \in Procs: weight[p] \geq 0
MsgWeightsPos     == \A p \in Procs: \A i \in 1..Len(chan[p]): chan[p][i].w > 0

Init ==
  /\ active = [p \in Procs |-> p = Leader]
  /\ weight = [p \in Procs |-> IF p = Leader THEN 1 ELSE 0]
  /\ chan   = [p \in Procs |-> << >>]
  /\ detected = FALSE

Send(p, q) ==
  /\ p \in Procs
  /\ q \in Procs \ {p}
  /\ active[p]
  /\ weight[p] > 0
  /\ weight'  = [weight EXCEPT ![p] = @ / 2]
  /\ chan'    = [chan EXCEPT ![q] = Append(@, [src |-> p, dst |-> q, w |-> weight[p] / 2])]
  /\ active'  = active
  /\ detected' = detected

Receive(q) ==
  /\ q \in Procs
  /\ Len(chan[q]) > 0
  /\ LET m == Head(chan[q]) IN
       /\ chan'    = [chan EXCEPT ![q] = Tail(@)]
       /\ weight'  = [weight EXCEPT ![q] = @ + m.w]
       /\ active'  = [active EXCEPT ![q] = TRUE]
       /\ detected' = detected

Idle(p) ==
  /\ p \in Procs
  /\ active[p]
  /\ active'  = [active EXCEPT ![p] = FALSE]
  /\ weight'  = weight
  /\ chan'    = chan
  /\ detected' = detected

Detect ==
  /\ ~active[Leader]
  /\ weight[Leader] = 1
  /\ detected' = TRUE
  /\ active'  = active
  /\ weight'  = weight
  /\ chan'    = chan

Next ==
  \/ \E p \in Procs: \E q \in Procs \ {p}: Send(p, q)
  \/ \E q \in Procs: Receive(q)
  \/ \E p \in Procs: Idle(p)
  \/ Detect

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Detect)
  /\ \A q \in Procs: WF_vars(Receive(q))
  /\ \A p \in Procs: WF_vars(Idle(p))

\* Safety properties
Safety_SumConserved == []SumInvariant
Safety_PositiveWeights == [](ProcWeightsNonNeg /\ MsgWeightsPos)
Safety_DetectedImpliesQuiescence == [](detected => (AllIdle /\ AllChannelsEmpty))

\* Liveness property: termination is eventually detected.
Liveness_EventualDetection == <>detected

=============================================================================