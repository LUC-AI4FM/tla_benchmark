```tla
MODULE MutualExclusionLock
EXTENDS Integers, TLC

CONSTANTS P1, P2, Null
VARIABLES pc1, pc2, turn, history, stutterCtrl

Init ==
  /\ pc1 = "start"
  /\ pc2 = "start"
  /\ turn = Null
  /\ history = <<>>
  /\ stutterCtrl = [p \in {P1, P2} |-> "inactive"]

Next ==
  \/ \* Process 1 entry protocol
    (pc1 = "start")
      /\ pc1' = "precritical1"
      /\ pc2' = pc2
      /\ turn' = turn
      /\ history' = history
      /\ stutterCtrl' = [stutterCtrl EXCEPT !P1 = "active"]
  \/ \* Process 1 precritical step 2
    (pc1 = "precritical1")
      /\ pc1' = "precritical2"
      /\ pc2' = pc2
      /\ turn' = turn
      /\ history' = history
      /\ stutterCtrl' = [stutterCtrl EXCEPT !P1 = "active"]
  \/ \* Process 1 set turn and enter critical section
    (pc1 = "precritical2")
      /\ pc1' = "critical"
      /\ pc2' = pc2
      /\ turn' = P2
      /\ history' = Append(history, P2)
      /\ stutterCtrl' = [stutterCtrl EXCEPT !P1 = "inactive"]
  \/ \* Process 1 exit critical section
    (pc1 = "critical")
      /\ pc1' = "exit"
      /\ pc2' = pc2
      /\ turn' = turn
      /\ history' = history
      /\ stutterCtrl' = [stutterCtrl EXCEPT !P1 = "inactive"]
  \/ \* Process 1 exit protocol
    (pc1 = "exit")
      /\ pc1' = "start"
      /\ pc2' = pc2
      /\ turn' = turn
      /\ history' = history
      /\ stutterCtrl' = [stutterCtrl EXCEPT !P1 = "inactive"]
  \/ \* Process 2 entry protocol
    (pc2 = "start")
      /\ pc2' = "precritical1"
      /\ pc1' = pc1
      /\ turn' = turn
      /\ history' = history
      /\ stutterCtrl' = [stutterCtrl EXCEPT !P2 = "active"]
  \/ \* Process 2 precritical step 2
    (pc2 = "precritical1")
      /\ pc2' = "precritical2"
      /\ pc1' = pc1
      /\ turn' = turn
      /\ history' = history
      /\ stutterCtrl' = [stutterCtrl EXCEPT !P2 = "active"]
  \/ \* Process 2 set turn and enter critical section
    (pc2 = "precritical2")
      /\ pc2' = "critical"
      /\ pc1' = pc1
      /\ turn' = P1
      /\ history' = Append(history, P1)
      /\ stutterCtrl' = [stutterCtrl EXCEPT !P2 = "inactive"]
  \/ \* Process 2 exit critical section
    (pc2 = "critical")
      /\ pc2' = "exit"
      /\ pc1' = pc1
      /\ turn' = turn
      /\ history' = history
      /\ stutterCtrl' = [stutterCtrl EXCEPT !P2 = "inactive"]
  \/ \* Process 2 exit protocol
    (pc2 = "exit")
      /\ pc2' = "start"
      /\ pc1' = pc1
      /\ turn' = turn
      /\ history' = history
      /\ stutterCtrl' = [stutterCtrl EXCEPT !P2 = "inactive"]
  \/ \* Stuttering step
    (pc1' = pc1)
      /\ (pc2' = pc2)
      /\ (turn' = turn)
      /\ (history' = history)
      /\ (stutterCtrl' = stutterCtrl)

Spec ==
  Init /\ [][Next]_<<pc1, pc2, turn, history, stutterCtrl>>

TypeInvariant ==
  /\ pc1 \in {"start", "precritical1", "precritical2", "critical", "exit"}
  /\ pc2 \in {"start", "precritical1", "precritical2", "critical", "exit"}
  /\ turn \in {P1, P2, Null}
  /\ history \in Seq({P1, P2})
  /\ stutterCtrl \in [p \in {P1, P2} |-> {"active", "inactive"}]

MutualExclusion ==
  ~((pc1 = "critical") /\ (pc2 = "critical"))

HistoryInvariant ==
  /\ \A p \in {P1, P2} : (pc[p] = "critical")
        => (stutterCtrl[p] = "inactive")
          /\ (Len(history) > 0)
          /\ ((p = P1) <=> (history[Len(history)] = P2))
  /\ \A p \in {P1, P2} : (stutterCtrl[p] = "active")
        => (pc[p] \in {"precritical1", "precritical2"})

Fairness ==
  <>(pc1 = "critical") /\ <>(pc2 = "critical")

THEOREM Spec => []TypeInvariant
THEOREM Spec => []MutualExclusion
THEOREM Spec => []HistoryInvariant
THEOREM Spec => Fairness

RefinementMapping ==
  [p \in {P1, P2} |-> IF pc[p] = "critical" THEN "critical"
                   ELSEIF pc[p] = "start" THEN "start"
                   ELSE "precritical"]

PetersonSpec ==
  /\ Init
  /\ [][Next]_<<pc1, pc2, turn>>
  /\ []TypeInvariant
  /\ []MutualExclusion

RefinementTheorem ==
  Spec => (PetersonSpec \* RefinementMapping)
```