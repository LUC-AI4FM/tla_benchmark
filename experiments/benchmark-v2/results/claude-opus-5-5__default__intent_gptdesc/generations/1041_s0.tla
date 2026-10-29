---------------------------- MODULE DijkstraMutex3 ----------------------------
(***************************************************************************)
(* Dijkstra's 1965 shared-memory mutual exclusion algorithm for three      *)
(* processes.  Processes communicate only through the shared variables b,  *)
(* c and k, and every action is atomic.  The model is asynchronous:        *)
(* scheduling is arbitrary, with fairness given explicitly in Spec.        *)
(*                                                                         *)
(* A process may stay in its noncritical section forever, so the ncs step  *)
(* is not given process-level fairness.                                    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N = 3

Procs == 1..N

VARIABLES
    b,          \* b[i] = FALSE iff process i is interested
    c,          \* c[i] = FALSE iff process i claims it is about to enter
    k,          \* the process that currently has "priority"
    pc,         \* program counter of each process
    unchecked   \* processes still to be checked in loop Li4b

vars == << b, c, k, pc, unchecked >>

Labels == {"Li0", "Li1", "Li2", "Li3a", "Li3b", "Li4a", "Li4b",
           "cs", "Li5", "Li6", "ncs"}

\* Locations where a process is trying to enter the critical section.
Trying == {"Li1", "Li2", "Li3a", "Li3b", "Li4a", "Li4b"}

TypeOK ==
    /\ b \in [Procs -> BOOLEAN]
    /\ c \in [Procs -> BOOLEAN]
    /\ k \in Procs
    /\ pc \in [Procs -> Labels]
    /\ unchecked \in [Procs -> SUBSET Procs]

Init ==
    /\ b = [i \in Procs |-> TRUE]
    /\ c = [i \in Procs |-> TRUE]
    /\ k \in Procs
    /\ pc = [i \in Procs |-> "Li0"]
    /\ unchecked = [i \in Procs |-> {}]

-----------------------------------------------------------------------------
(* Process actions *)

\* Announce interest.
Li0(self) ==
    /\ pc[self] = "Li0"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "Li1"]
    /\ UNCHANGED << c, k, unchecked >>

\* If I do not have priority, try to get it; otherwise go to the check phase.
Li1(self) ==
    /\ pc[self] = "Li1"
    /\ IF k # self
         THEN pc' = [pc EXCEPT ![self] = "Li2"]
         ELSE pc' = [pc EXCEPT ![self] = "Li4a"]
    /\ UNCHANGED << b, c, k, unchecked >>

Li2(self) ==
    /\ pc[self] = "Li2"
    /\ c' = [c EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "Li3a"]
    /\ UNCHANGED << b, k, unchecked >>

\* Read b[k]: if the priority holder is not interested, grab priority.
Li3a(self) ==
    /\ pc[self] = "Li3a"
    /\ IF b[k]
         THEN pc' = [pc EXCEPT ![self] = "Li3b"]
         ELSE pc' = [pc EXCEPT ![self] = "Li1"]
    /\ UNCHANGED << b, c, k, unchecked >>

Li3b(self) ==
    /\ pc[self] = "Li3b"
    /\ k' = self
    /\ pc' = [pc EXCEPT ![self] = "Li1"]
    /\ UNCHANGED << b, c, unchecked >>

\* Claim entry and prepare to check all other processes.
Li4a(self) ==
    /\ pc[self] = "Li4a"
    /\ c' = [c EXCEPT ![self] = FALSE]
    /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
    /\ pc' = [pc EXCEPT ![self] = "Li4b"]
    /\ UNCHANGED << b, k >>

\* Check the other processes one at a time; restart if any has a claim.
Li4b(self) ==
    /\ pc[self] = "Li4b"
    /\ IF unchecked[self] # {}
         THEN \E j \in unchecked[self] :
                /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {j}]
                /\ IF ~c[j]
                     THEN pc' = [pc EXCEPT ![self] = "Li1"]
                     ELSE pc' = [pc EXCEPT ![self] = "Li4b"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
              /\ UNCHANGED unchecked
    /\ UNCHANGED << b, c, k >>

\* Critical section.
CS(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "Li5"]
    /\ UNCHANGED << b, c, k, unchecked >>

Li5(self) ==
    /\ pc[self] = "Li5"
    /\ c' = [c EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "Li6"]
    /\ UNCHANGED << b, k, unchecked >>

Li6(self) ==
    /\ pc[self] = "Li6"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED << c, k, unchecked >>

\* Noncritical section.  No fairness: a process may stay here forever.
NCS(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "Li0"]
    /\ UNCHANGED << b, c, k, unchecked >>

\* All steps of a process except the noncritical-section step.
Step(self) ==
    \/ Li0(self) \/ Li1(self) \/ Li2(self) \/ Li3a(self) \/ Li3b(self)
    \/ Li4a(self) \/ Li4b(self) \/ CS(self) \/ Li5(self) \/ Li6(self)

Proc(self) == Step(self) \/ NCS(self)

\* Arbitrary interleaving of the processes' atomic steps.
Next == \E self \in Procs : Proc(self)

-----------------------------------------------------------------------------
(* Fairness: each process that can take a non-ncs step is not delayed      *)
(* forever.  The system as a whole is also not allowed to halt while some  *)
(* step is enabled.                                                        *)

Fairness ==
    /\ \A self \in Procs : WF_vars(Step(self))
    /\ WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety *)

InCS(i) == pc[i] = "cs"

MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(InCS(i) /\ InCS(j))

\* Equivalent form: at most one process in the critical section.
AtMostOneInCS == Cardinality({i \in Procs : InCS(i)}) <= 1

Inv == TypeOK /\ MutualExclusion /\ AtMostOneInCS

-----------------------------------------------------------------------------
(* Liveness *)

\* If some process is trying to enter, then some process eventually
\* enters the critical section.  This rules out all contenders being
\* starved together.
DeadlockFreedom ==
    (\E i \in Procs : pc[i] \in Trying) ~> (\E i \in Procs : InCS(i))

\* Some step of the system is always possible (no deadlocked state).
NoDeadlock == [](ENABLED Next)

\* If some process is enabled, some process eventually takes a step.
Progress == [](ENABLED <<Next>>_vars => <><<Next>>_vars)

\* A process that enters the critical section eventually leaves it.
CSExit == \A i \in Procs : InCS(i) ~> (pc[i] = "ncs")

-----------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => DeadlockFreedom
THEOREM Spec => NoDeadlock
THEOREM Spec => Progress
THEOREM Spec => CSExit
=============================================================================