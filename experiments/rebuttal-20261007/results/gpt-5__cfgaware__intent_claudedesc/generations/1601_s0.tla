---- MODULE Fischer ----
EXTENDS Integers, TLC

CONSTANTS 
  N, \* number of processes (positive integer)
  Delta, \* timer delay before writing the identifier
  Epsilon  \* timer delay before re-checking after writing

ASSUME /\ N \in Nat \ {0}
       /\ Delta \in Nat
       /\ Epsilon \in Nat

Proc == 1..N

VARIABLES 
  X,     \* shared integer variable: 0 means free, i in Proc means last writer i
  pc,    \* program counter per process
  t      \* per-process timer (natural number; 0 means the process' current wait has expired)

vars == << X, pc, t >>

Init ==
  /\ X = 0
  /\ pc \in [Proc -> {"idle", "waitDelta", "waitEps", "cs"}]
  /\ \A i \in Proc : pc[i] = "idle"
  /\ t \in [Proc -> Nat]
  /\ \A i \in Proc : t[i] = 1

\* Global clock: decrements all timers by one when every timer is strictly positive.
Tick ==
  /\ \A i \in Proc : t[i] > 0
  /\ t' = [i \in Proc |-> t[i] - 1]
  /\ UNCHANGED << X, pc >>

\* Process i actions
Claim(i) ==
  /\ i \in Proc
  /\ pc[i] = "idle"
  /\ X = 0
  /\ pc' = [pc EXCEPT ![i] = "waitDelta"]
  /\ t'  = [t  EXCEPT ![i] = Delta]
  /\ UNCHANGED X

WriteId(i) ==
  /\ i \in Proc
  /\ pc[i] = "waitDelta"
  /\ t[i] = 0
  /\ pc' = [pc EXCEPT ![i] = "waitEps"]
  /\ t'  = [t  EXCEPT ![i] = Epsilon]
  /\ X' = i

CheckEnter(i) ==
  /\ i \in Proc
  /\ pc[i] = "waitEps"
  /\ t[i] = 0
  /\ IF X = i
        THEN /\ pc' = [pc EXCEPT ![i] = "cs"]
             /\ UNCHANGED X
        ELSE /\ pc' = [pc EXCEPT ![i] = "idle"]
             /\ UNCHANGED X
  /\ t'  = [t  EXCEPT ![i] = 1]

ExitCS(i) ==
  /\ i \in Proc
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ X' = 0
  /\ t' = [t EXCEPT ![i] = 1]

ProcAct(i) == Claim(i) \/ WriteId(i) \/ CheckEnter(i) \/ ExitCS(i)

Next ==
  \/ Tick
  \/ \E i \in Proc : ProcAct(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in Proc : WF_vars(ProcAct(i))
  /\ WF_vars(Tick)

\* Safety: mutual exclusion — never two distinct processes in the critical section simultaneously.
InCS(i) == pc[i] = "cs"
MutualExclusion ==
  \A i \in Proc : \A j \in Proc : i # j => ~(InCS(i) /\ InCS(j))

Invariant == MutualExclusion

\* Liveness: some process enters the critical section infinitely often.
Liveness == []<>(\E i \in Proc : InCS(i))

====