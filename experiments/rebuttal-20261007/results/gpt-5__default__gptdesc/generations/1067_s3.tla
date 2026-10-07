----------------------------- MODULE RingTermination -----------------------------

EXTENDS Naturals, Sequences

CONSTANTS Node, RingSeq

NoDups(s) == \A i, j \in 1..Len(s): (i /= j) => (s[i] /= s[j])

NodeFromSeq(s) == { s[i] : i \in 1..Len(s) }

ASSUME
  /\ Len(RingSeq) >= 1
  /\ NoDups(RingSeq)
  /\ Node = NodeFromSeq(RingSeq)

N == Len(RingSeq)

Pos(n) == CHOOSE i \in 1..N: RingSeq[i] = n

Succ(n) == IF Pos(n) = N THEN RingSeq[1] ELSE RingSeq[Pos(n)+1]

VARIABLES active, detected

vars == << active, detected >>

Quiescent == \A n \in Node: ~active[n]

TypeInv ==
  /\ active \in [Node -> BOOLEAN]
  /\ detected \in BOOLEAN

Init ==
  /\ TypeInv
  /\ detected = FALSE

Terminate(n) ==
  /\ n \in Node
  /\ active[n]
  /\ active' = [active EXCEPT ![n] = FALSE]
  /\ detected' = detected

Wake(n) ==
  /\ n \in Node
  /\ active[n]
  /\ ~active[Succ(n)]
  /\ active' = [active EXCEPT ![Succ(n)] = TRUE]
  /\ detected' = detected

DetectAction ==
  /\ Quiescent
  /\ ~detected
  /\ detected' = TRUE
  /\ active' = active

Next ==
  \/ \E n \in Node: Terminate(n)
  \/ \E n \in Node: Wake(n)
  \/ DetectAction

Spec == Init /\ [][Next]_vars /\ WF_vars(DetectAction)

Safety_Correctness == [](detected => Quiescent)

TypeOK == []TypeInv

StableDetection == [](detected => detected')

Liveness_QuiescentImpliesDetection == [](Quiescent => <>detected)

Liveness_EventualQuiescenceImpliesDetection == (<>[]Quiescent) => (<>detected)

===============================================================================