------------------------------ MODULE HuangTermination ------------------------------

EXTENDS Naturals, Sequences

CONSTANTS
  Procs,        \* finite, nonempty set of processes
  Leader,       \* designated initiator process in Procs
  None          \* a distinguished value not in Procs, used as "no parent"

ASSUME Leader \in Procs
ASSUME None \notin Procs

VARIABLES
  active,       \* [Procs -> BOOLEAN]: whether a process is active (has work)
  parent,       \* [Procs -> (Procs \cup {None})]: parent pointer for weight return
  weightProc,   \* [Procs -> Real]: local weight held by each process
  work,         \* [Procs -> [Procs -> Real]]: in-transit work weights from src->dst
  ret,          \* [Procs -> [Procs -> Real]]: in-transit return weights from src->dst (child->parent)
  detected      \* BOOLEAN: whether the leader has detected global termination

vars == << active, parent, weightProc, work, ret, detected >>

\* Generic summation over a finite set S with function F
RECURSIVE Sum(_,_)
Sum(F, S) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE y \in S: TRUE IN
      F[x] + Sum(F, S \ {x})

WorkPairs == { <<p, q>> \in Procs \X Procs : TRUE }

WorkSum ==
  Sum(LAMBDA pq:
        LET p == pq[1] IN
        LET q == pq[2] IN work[p][q],
      WorkPairs)

RetSum ==
  Sum(LAMBDA pq:
        LET p == pq[1] IN
        LET q == pq[2] IN ret[p][q],
      WorkPairs)

WeightSum ==
  Sum(LAMBDA p: weightProc[p], Procs)

AllIdle == \A p \in Procs: ~active[p]

ChannelsEmpty == \A p \in Procs: \A q \in Procs: work[p][q] = 0 /\ ret[p][q] = 0

TypeOK ==
  /\ active \in [Procs -> BOOLEAN]
  /\ parent \in [Procs -> (Procs \cup {None})]
  /\ weightProc \in [Procs -> Real]
  /\ work \in [Procs -> [Procs -> Real]]
  /\ ret \in [Procs -> [Procs -> Real]]
  /\ detected \in BOOLEAN

NonNegativity ==
  /\ \A p \in Procs: weightProc[p] >= 0
  /\ \A p \in Procs: \A q \in Procs: work[p][q] >= 0 /\ ret[p][q] >= 0

WeightConservation ==
  WeightSum + WorkSum + RetSum = 1

DetectedSoundness ==
  detected => (AllIdle /\ ChannelsEmpty)

Init ==
  /\ TypeOK
  /\ active = [p \in Procs |-> IF p = Leader THEN TRUE ELSE FALSE]
  /\ parent = [p \in Procs |-> None]
  /\ weightProc = [p \in Procs |-> IF p = Leader THEN 1 ELSE 0]
  /\ work = [p \in Procs |-> [q \in Procs |-> 0]]
  /\ ret = [p \in Procs |-> [q \in Procs |-> 0]]
  /\ detected = FALSE
  /\ NonNegativity
  /\ WeightConservation

SendWork(p, q) ==
  /\ p \in Procs /\ q \in Procs /\ p # q
  /\ active[p]
  /\ weightProc[p] > 0
  /\ LET w == weightProc[p] / 2 IN
       /\ active' = [active EXCEPT ! = @]
       /\ parent' = parent
       /\ weightProc' = [weightProc EXCEPT ![p] = weightProc[p] - w]
       /\ work' = [work EXCEPT ![p][q] = work[p][q] + w]
       /\ ret' = ret
       /\ detected' = detected

ReceiveWork(p, q) ==
  /\ p \in Procs /\ q \in Procs
  /\ work[p][q] > 0
  /\ LET w == work[p][q] IN
       /\ work' = [work EXCEPT ![p][q] = work[p][q] - w]
       /\ weightProc' = [weightProc EXCEPT ![q] = weightProc[q] + w]
       /\ active' = [active EXCEPT ![q] = TRUE]
       /\ parent' = [parent EXCEPT ![q] = IF active[q] THEN parent[q] ELSE p]
       /\ ret' = ret
       /\ detected' = detected

BecomeIdle(p) ==
  /\ p \in Procs
  /\ active[p]
  /\ active' = [active EXCEPT ![p] = FALSE]
  /\ UNCHANGED << parent, weightProc, work, ret, detected >>

ReturnWeight(p) ==
  /\ p \in Procs
  /\ ~active[p]
  /\ parent[p] \in Procs
  /\ weightProc[p] > 0
  /\ ret' = [ret EXCEPT ![p][parent[p]] = ret[p][parent[p]] + weightProc[p]]
  /\ weightProc' = [weightProc EXCEPT ![p] = 0]
  /\ UNCHANGED << active, parent, work, detected >>

ReceiveReturn(p, q) ==
  /\ p \in Procs /\ q \in Procs
  /\ ret[p][q] > 0
  /\ LET w == ret[p][q] IN
       /\ ret' = [ret EXCEPT ![p][q] = 0]
       /\ weightProc' = [weightProc EXCEPT ![q] = weightProc[q] + w]
       /\ UNCHANGED << active, parent, work, detected >>

Detect ==
  /\ ~detected
  /\ AllIdle
  /\ ChannelsEmpty
  /\ parent[Leader] = None
  /\ weightProc[Leader] = 1
  /\ detected' = TRUE
  /\ UNCHANGED << active, parent, weightProc, work, ret >>

Next ==
  \E p \in Procs:
    \/ \E q \in Procs: SendWork(p, q)
    \/ BecomeIdle(p)
    \/ ReturnWeight(p)
    \/ \E q \in Procs: ReceiveWork(p, q)
    \/ \E q \in Procs: ReceiveReturn(p, q)
  \/ Detect

Fairness ==
  /\ \A p \in Procs: \A q \in Procs:
       WF_vars(ReceiveWork(p, q))
  /\ \A p \in Procs: \A q \in Procs:
       WF_vars(ReceiveReturn(p, q))
  /\ \A p \in Procs:
       WF_vars(ReturnWeight(p))
  /\ \A p \in Procs:
       WF_vars(BecomeIdle(p))
  /\ WF_vars(Detect)

Spec ==
  Init /\ [][Next]_vars /\ Fairness

\* Safety properties (invariants)
Inv ==
  /\ TypeOK
  /\ NonNegativity
  /\ WeightConservation
  /\ DetectedSoundness

\* Liveness: eventual detection (under fairness/progress assumptions)
TerminationLiveness ==
  <> detected

\* Stronger conditional liveness: if the system ever becomes quiescent, detection follows
QuiescenceImpliesDetection ==
  (<> (AllIdle /\ ChannelsEmpty)) => (<> detected)

=============================================================================