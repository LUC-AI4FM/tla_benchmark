---------------------------- MODULE RoundRobinMutex ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N > 0

Procs == 0 .. (N - 1)

States == {"nc", "wait", "cs", "exit"}

VARIABLES pc, turn

vars == << pc, turn >>

TypeOK ==
    /\ pc \in [Procs -> States]
    /\ turn \in Procs

Init ==
    /\ pc = [p \in Procs |-> "nc"]
    /\ turn = 0

\* Noncritical work finished; start trying to enter
Try(p) ==
    /\ pc[p] = "nc"
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED turn

\* Enter the critical section only when holding the token
Enter(p) ==
    /\ pc[p] = "wait"
    /\ turn = p
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED turn

\* Leave the critical section
Leave(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED turn

\* Hand the token to the successor in modulo-N order
Advance(p) ==
    /\ pc[p] = "exit"
    /\ turn = p
    /\ turn' = (p + 1) % N
    /\ pc' = [pc EXCEPT ![p] = "nc"]

Proc(p) == Try(p) \/ Enter(p) \/ Leave(p) \/ Advance(p)

Next == \E p \in Procs : Proc(p)

Fairness == \A p \in Procs : WF_vars(Proc(p))

Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
\* Safety properties

\* Mutual exclusion: no two processes simultaneously in the critical section
cs == \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

MutualExclusion == cs

TurnValid == turn \in Procs

\* Only the token holder may be in cs or exit
TokenInvariant ==
    \A p \in Procs : pc[p] \in {"cs", "exit"} => turn = p

Inv == TypeOK /\ TurnValid /\ cs /\ TokenInvariant

\* Control states follow the cycle nc -> wait -> cs -> exit -> nc
NextState(s) ==
    CASE s = "nc"   -> "wait"
      [] s = "wait" -> "cs"
      [] s = "cs"   -> "exit"
      [] s = "exit" -> "nc"

CycleOrder ==
    [][\A p \in Procs : pc'[p] # pc[p] => pc'[p] = NextState(pc[p])]_vars

TurnAdvance ==
    [][turn' # turn => turn' = (turn + 1) % N]_vars

----------------------------------------------------------------------------
\* Liveness properties

\* Every waiting process eventually enters its critical section
StarvationFreedom ==
    \A p \in Procs : (pc[p] = "wait") ~> (pc[p] = "cs")

\* Every process gets the token infinitely often
TokenInfinitelyOften ==
    \A p \in Procs : []<>(turn = p)

\* Every process enters the critical section infinitely often
CSInfinitelyOften ==
    \A p \in Procs : []<>(pc[p] = "cs")

=============================================================================