---- MODULE RoundRobinMutex ----
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N > 0

Procs == 0 .. (N - 1)

States == {"noncritical", "waiting", "critical", "exit"}

\* Expected control-state cycle: noncritical -> waiting -> critical -> exit -> noncritical
NextState(s) ==
    CASE s = "noncritical" -> "waiting"
      [] s = "waiting"     -> "critical"
      [] s = "critical"    -> "exit"
      [] s = "exit"        -> "noncritical"

VARIABLES turn, pc

vars == << turn, pc >>

TypeOK ==
    /\ turn \in Procs
    /\ pc \in [Procs -> States]

Init ==
    /\ turn \in Procs
    /\ pc = [p \in Procs |-> "noncritical"]

\* A process finishes noncritical work and starts trying to enter.
Try(p) ==
    /\ pc[p] = "noncritical"
    /\ pc' = [pc EXCEPT ![p] = "waiting"]
    /\ UNCHANGED turn

\* A process may enter only when the token equals its id.
Enter(p) ==
    /\ pc[p] = "waiting"
    /\ turn = p
    /\ pc' = [pc EXCEPT ![p] = "critical"]
    /\ UNCHANGED turn

\* A process leaves its critical section.
Leave(p) ==
    /\ pc[p] = "critical"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED turn

\* A process hands the token to its successor in modulo-N order.
Advance(p) ==
    /\ pc[p] = "exit"
    /\ turn' = (p + 1) % N
    /\ pc' = [pc EXCEPT ![p] = "noncritical"]

Proc(p) == Try(p) \/ Enter(p) \/ Leave(p) \/ Advance(p)

Next == \E p \in Procs : Proc(p)

Fairness == \A p \in Procs : WF_vars(Proc(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

\* No two processes are simultaneously in the critical section.
MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "critical" /\ pc[q] = "critical")

\* The turn is always a valid process id.
TurnValid == turn \in Procs

\* Only the token holder can be in the critical or exit region.
TokenHolder ==
    \A p \in Procs : pc[p] \in {"critical", "exit"} => turn = p

\* At most one process is in the critical or exit region.
AtMostOneInRegion ==
    Cardinality({p \in Procs : pc[p] \in {"critical", "exit"}}) <= 1

\* Every control-state change follows the expected cycle.
CycleOrder ==
    [][\A p \in Procs : pc'[p] # pc[p] => pc'[p] = NextState(pc[p])]_vars

\* The turn only changes by advancing to the successor of its current value.
TurnAdvance ==
    [][turn' # turn => turn' = (turn + 1) % N]_vars

Inv ==
    /\ TypeOK
    /\ TurnValid
    /\ MutualExclusion
    /\ TokenHolder
    /\ AtMostOneInRegion

-----------------------------------------------------------------------------
\* Liveness properties

\* If a process is waiting and the token equals its id, it eventually enters.
EnterWhenEnabled ==
    \A p \in Procs : (pc[p] = "waiting" /\ turn = p) ~> (pc[p] = "critical")

\* Starvation freedom: every waiting process eventually enters its critical section.
StarvationFreedom ==
    \A p \in Procs : (pc[p] = "waiting") ~> (pc[p] = "critical")

\* Every process is given the token infinitely often.
TokenInfinitelyOften ==
    \A p \in Procs : []<>(turn = p)

\* Every process enters its critical section infinitely often.
CriticalInfinitelyOften ==
    \A p \in Procs : []<>(pc[p] = "critical")

THEOREM Spec => []Inv
THEOREM Spec => CycleOrder /\ TurnAdvance
THEOREM Spec => EnterWhenEnabled /\ StarvationFreedom
                /\ TokenInfinitelyOften /\ CriticalInfinitelyOften
=============================================================================