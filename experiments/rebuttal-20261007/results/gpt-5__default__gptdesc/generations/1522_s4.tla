------------------------------ MODULE HuangsTermination ------------------------------

EXTENDS Naturals, Sequences

CONSTANTS
  Procs,        \* Finite, nonempty set of processes
  Leader,       \* Distinguished initiator process, element of Procs
  K             \* Natural, determines total initial weight Denom = 2^K

ASSUME /\ Leader \in Procs
       /\ Procs # {}
       /\ K \in Nat

RECURSIVE Pow2(_)
Pow2(k) ==
  IF k = 0 THEN 1 ELSE 2 * Pow2(k - 1)

Denom == Pow2(K)

\* Message type: work messages carry weight to a process; return messages return weight to the Leader
Msg == [from : Procs, w : Nat, kind : {"work", "ret"}]

VARIABLES
  active,    \* [Procs -> BOOLEAN]
  weight,    \* [Procs -> Nat], scaled so that total weight Denom represents 1
  inQ,       \* [Procs -> Seq(Msg)], each process's incoming message queue
  detected   \* BOOLEAN

vars == << active, weight, inQ, detected >>

\* Helpers to sum weights across processes and queued messages
RECURSIVE SumSeqWeights(_)
SumSeqWeights(s) ==
  IF Len(s) = 0 THEN 0 ELSE s[1].w + SumSeqWeights(Tail(s))

RECURSIVE SumOverProcs(_, _)
SumOverProcs(f, S) ==
  IF S = {} THEN 0
  ELSE
    LET p == CHOOSE x \in S : TRUE IN
      f[p] + SumOverProcs(f, S \ {p})

SumProcWeights == SumOverProcs(weight, Procs)
SumInQWeights == SumOverProcs([p \in Procs |-> SumSeqWeights(inQ[p])], Procs)

AllIdle == \A p \in Procs : active[p] = FALSE
AllQueuesEmpty == \A p \in Procs : Len(inQ[p]) = 0

\* Initialization: Leader holds all weight and is active; others idle with zero weight; no messages; not detected
Init ==
  /\ active = [p \in Procs |-> p = Leader]
  /\ weight = [p \in Procs |-> IF p = Leader THEN Denom ELSE 0]
  /\ inQ    = [p \in Procs |-> << >>]
  /\ detected = FALSE

\* Actions

SendWork(p, q) ==
  /\ p \in Procs /\ q \in Procs /\ p # q
  /\ active[p] = TRUE
  /\ weight[p] >= 2
  /\ LET w == weight[p] \div 2 IN
       /\ inQ' = [inQ EXCEPT ![q] = Append(@, [from |-> p, w |-> w, kind |-> "work"])]
       /\ weight' = [weight EXCEPT ![p] = @ - w]
       /\ UNCHANGED << active, detected >>

Receive(p) ==
  /\ p \in Procs
  /\ Len(inQ[p]) > 0
  /\ LET m == Head(inQ[p]) IN
       /\ IF m.kind = "work" THEN
            /\ weight' = [weight EXCEPT ![p] = @ + m.w]
            /\ active' = [active EXCEPT ![p] = TRUE]
          ELSE
            /\ p = Leader
            /\ weight' = [weight EXCEPT ![Leader] = @ + m.w]
            /\ UNCHANGED active
       /\ inQ' = [inQ EXCEPT ![p] = Tail(@)]
       /\ UNCHANGED detected

ReturnWeight(p) ==
  /\ p \in Procs \ {Leader}
  /\ active[p] = FALSE
  /\ weight[p] > 0
  /\ inQ' = [inQ EXCEPT ![Leader] = Append(@, [from |-> p, w |-> weight[p], kind |-> "ret"])]
  /\ weight' = [weight EXCEPT ![p] = 0]
  /\ UNCHANGED << active, detected >>

\* When a process is active, has no pending incoming messages, and cannot send (weight < 2),
\* it may complete and become idle.
Complete(p) ==
  /\ p \in Procs
  /\ active[p] = TRUE
  /\ Len(inQ[p]) = 0
  /\ weight[p] < 2
  /\ active' = [active EXCEPT ![p] = FALSE]
  /\ UNCHANGED << weight, inQ, detected >>

\* The Leader detects termination when it is idle, all are idle, no messages remain, and it holds all weight.
Detect ==
  /\ detected = FALSE
  /\ active[Leader] = FALSE
  /\ \A p \in Procs : active[p] = FALSE
  /\ \A p \in Procs : Len(inQ[p]) = 0
  /\ weight[Leader] = Denom
  /\ detected' = TRUE
  /\ UNCHANGED << active, weight, inQ >>

Next ==
  \/ \E p \in Procs : Receive(p)
  \/ \E p \in Procs : \E q \in Procs \ {p} : SendWork(p, q)
  \/ \E p \in Procs \ {Leader} : ReturnWeight(p)
  \/ \E p \in Procs : Complete(p)
  \/ Detect
  \/ UNCHANGED vars

\* Fairness to ensure progress: messages are eventually received, idle processes eventually return weight,
\* processes that can complete eventually do, and detection eventually happens when enabled.
Fairness ==
  /\ \A p \in Procs : WF_vars(Receive(p))
  /\ \A p \in Procs \ {Leader} : SF_vars(ReturnWeight(p))
  /\ \A p \in Procs : SF_vars(Complete(p))
  /\ SF_vars(Detect)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Fairness

\* Safety invariants

TypeOK ==
  /\ active \in [Procs -> BOOLEAN]
  /\ weight \in [Procs -> Nat]
  /\ inQ \in [Procs -> Seq(Msg)]
  /\ detected \in BOOLEAN

WeightConservation ==
  SumProcWeights + SumInQWeights = Denom

\* All return-weight messages reside only in the Leader's queue
ReturnMsgsOnlyToLeader ==
  \A p \in Procs \ {Leader} :
    \A i \in 1..Len(inQ[p]) : inQ[p][i].kind = "work"

Safety ==
  /\ []TypeOK
  /\ []WeightConservation
  /\ []ReturnMsgsOnlyToLeader
  /\ [](detected => /\ AllIdle /\ AllQueuesEmpty)

\* Liveness: termination is eventually detected
Liveness == <>detected

=============================================================================