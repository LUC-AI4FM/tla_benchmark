---------------------------- MODULE HuangTermination ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Procs, Leader
VARIABLE weight, msgQueue, active

TypeOK == 
  /\ weight \in [Procs -> {x \in Rational : x >= 0}]
  /\ msgQueue \in [Procs -> SUBSET (Procs \X Rational)]
  /\ active \in [Procs -> BOOLEAN]

StateConstraint == 
  /\ TypeOK
  /\ (forall <<p, w>> \in msgQueue : w > 0)
  /\ (forall p \in Procs : weight[p] > 0)

WeightConservation == 
  LET sumWeights == +<<weight[p] | p \in Procs>>
      sumMsgs    == +<<w | <<_, w>> \in Union {msgQueue[p] : p \in Procs}>>
  IN sumWeights + sumMsgs = 1

Init == 
  /\ weight = [p \in Procs |-> IF p = Leader THEN 1 ELSE 0]
  /\ msgQueue = [p \in Procs |-> {}]
  /\ active = [p \in Procs |-> IF p = Leader THEN TRUE ELSE FALSE]

Send(p, q) == 
  /\ weight[p] > 0
  /\ p \in Procs
  /\ q \in Procs
  /\ weight' = [weight EXCEPT ![p] = @ / 2]
  /\ msgQueue' = [msgQueue EXCEPT ![q] = @ \union {[p, @ / 2]}]
  /\ active' = active

Rcv(p) == 
  /\ ~active[p]
  /\ msgQueue[p] # {}
  /\ LET <<q, w>> == CHOOSE <<_, _>> \in msgQueue[p] : TRUE
  IN
    /\ weight' = [weight EXCEPT ![p] = @ + w]
    /\ msgQueue' = [msgQueue EXCEPT ![p] = @ \ {<<q, w>>}]
    /\ active' = [active EXCEPT ![p] = TRUE]

Idle(p) == 
  /\ p # Leader
  /\ weight[p] > 0
  /\ weight' = [weight EXCEPT ![Leader] = @ + weight[p], ![p] = 0]
  /\ msgQueue' = [msgQueue EXCEPT ![Leader] = @ \union {[p, weight[p]]}]
  /\ active' = [active EXCEPT ![p] = FALSE]

IdleLdr == 
  /\ active[Leader]
  /\ active' = [active EXCEPT ![Leader] = FALSE]
  /\ UNCHANGED <<weight, msgQueue>>

RcvLdr == 
  /\ ~active[Leader]
  /\ msgQueue[Leader] # {}
  /\ LET <<q, w>> == CHOOSE <<_, _>> \in msgQueue[Leader] : TRUE
  IN
    /\ weight' = [weight EXCEPT ![Leader] = @ + w]
    /\ msgQueue' = [msgQueue EXCEPT ![Leader] = @ \ {<<q, w>>}]
    /\ active' = active

Next == 
  \/ (\E p, q \in Procs : Send(p, q))
  \/ (\E p \in Procs : Rcv(p))
  \/ (\E p \in (Procs \ {Leader}) : Idle(p))
  \/ IdleLdr
  \/ RcvLdr

Spec == 
  /\ Init
  /\ [][Next]_<<weight, msgQueue, active>>
  /\ WF_<<weight, msgQueue, active>>(\E p \in Procs : Rcv(p))
  /\ WF_<<weight, msgQueue, active>>(\E p \in (Procs \ {Leader}) : Idle(p))

Safe == 
  []((active[Leader] = FALSE /\ weight[Leader] = 1) => 
      (forall p \in Procs : active[p] = FALSE) 
      /\ (forall p \in Procs : msgQueue[p] = {}))

Live == 
  <>((active[Leader] = FALSE /\ weight[Leader] = 1) 
      /\ (forall p \in Procs : active[p] = FALSE) 
      /\ (forall p \in Procs : msgQueue[p] = {}))

THEOREM Spec => []Safe
THEOREM Spec => Live

===============================================================================