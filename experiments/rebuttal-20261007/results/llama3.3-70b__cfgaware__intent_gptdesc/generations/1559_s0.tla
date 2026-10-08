--------------------------- MODULE MutualExclusion ---------------------------
EXTENDS Integers, TLC

CONSTANT ProcessSet
VARIABLE pc, turn, history, stutterCtrl

TypeOKHS == 
  /\ pc \in [ProcessSet -> {"start", "precritical1", "precritical2", "critical", "exit"}]
  /\ turn \in ProcessSet
  /\ history \in [ProcessSet -> ProcessSet]
  /\ stutterCtrl \in [ProcessSet -> {"inactive", "active"}]

InvHS == 
  /\ TypeOKHS
  /\ LockInv
  /\ \A p \in ProcessSet : 
      (pc[p] = "critical" /\ stutterCtrl[p] = "active") => 
        (history[p] = (if p = 1 then 2 else 1))

LockInv == 
  /\ ~(\E p1, p2 \in ProcessSet : pc[p1] = "critical" /\ pc[p2] = "critical" /\ p1 # p2)
  /\ \A p \in ProcessSet : (pc[p] = "critical") => (turn = (if p = 1 then 2 else 1))

SpecHS == 
  /\ TypeOKHS
  /\ [][
      /\ \E p \in ProcessSet :
          \/ /\ pc[p] = "start"
              /\ pc' = [pc EXCEPT ![p] = "precritical1"]
              /\ turn' = turn
              /\ history' = history
              /\ stutterCtrl' = [stutterCtrl EXCEPT ![p] = "active"]
          \/ /\ pc[p] = "precritical1"
              /\ pc' = [pc EXCEPT ![p] = "precritical2"]
              /\ turn' = turn
              /\ history' = history
              /\ stutterCtrl' = stutterCtrl
          \/ /\ pc[p] = "precritical2"
              /\ turn' = (if p = 1 then 2 else 1)
              /\ history' = [history EXCEPT ![p] = turn']
              /\ pc' = [pc EXCEPT ![p] = "critical"]
              /\ stutterCtrl' = [stutterCtrl EXCEPT ![p] = "inactive"]
          \/ /\ pc[p] = "critical"
              /\ pc' = [pc EXCEPT ![p] = "exit"]
              /\ turn' = turn
              /\ history' = history
              /\ stutterCtrl' = stutterCtrl
          \/ /\ pc[p] = "exit"
              /\ pc' = [pc EXCEPT ![p] = "start"]
              /\ turn' = turn
              /\ history' = history
              /\ stutterCtrl' = stutterCtrl
      /\ \A q \in ProcessSet :
          (pc[q] = "critical" /\ stutterCtrl[q] = "active") => 
            (history[q] = (if q = 1 then 2 else 1))
  ]

Spec == 
  /\ SpecHS
  /\ WF_vars({pc, turn, history, stutterCtrl}, SpecHS)

PSpec == 
  /\ [][
      /\ \E p \in ProcessSet :
          \/ /\ pc[p] = "start"
              /\ pc' = [pc EXCEPT ![p] = "critical"]
              /\ turn' = (if p = 1 then 2 else 1)
          \/ /\ pc[p] = "critical"
              /\ pc' = [pc EXCEPT ![p] = "exit"]
          \/ /\ pc[p] = "exit"
              /\ pc' = [pc EXCEPT ![p] = "start"]
      /\ \A p, q \in ProcessSet : 
          (pc[p] = "critical" /\ pc[q] = "critical") => (p = q)
  ]

=============================================================================