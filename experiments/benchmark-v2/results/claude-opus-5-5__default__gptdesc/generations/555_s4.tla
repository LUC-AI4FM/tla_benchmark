------------------------------ MODULE MCSession9sem ------------------------------
(***************************************************************************)
(* Model-checking wrapper for the Session9sem semaphore-based mutual       *)
(* exclusion protocol.  It fixes the number of processes to 3 and defines  *)
(* the process set as 0..(ConstN-1).  It states mutual exclusion as a      *)
(* safety property, and deadlock/livelock freedom and starvation freedom   *)
(* as leads-to liveness properties over the control-state variable pc.     *)
(*                                                                         *)
(* The underlying Session9sem protocol is included inline, so the module   *)
(* is self-contained and parses on its own.                                *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

\* Concrete constants for model checking
ConstN == 3

Procs == 0..(ConstN - 1)

VARIABLES sem,  \* binary semaphore guarding the critical section
          pc    \* control state of each process

vars == << sem, pc >>

Labels == {"ncs", "enter", "cs", "exit"}

TypeOK ==
    /\ sem \in {0, 1}
    /\ pc \in [Procs -> Labels]

----------------------------------------------------------------------------
(* Session9sem protocol *)

Init ==
    /\ sem = 1
    /\ pc = [i \in Procs |-> "ncs"]

\* Leave the noncritical section and request entry (may never happen)
Request(i) ==
    /\ pc[i] = "ncs"
    /\ pc' = [pc EXCEPT ![i] = "enter"]
    /\ UNCHANGED sem

\* P(sem): wait until the semaphore is free, then acquire it
Enter(i) ==
    /\ pc[i] = "enter"
    /\ sem = 1
    /\ sem' = 0
    /\ pc' = [pc EXCEPT ![i] = "cs"]

\* Finish the critical section
LeaveCS(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ UNCHANGED sem

\* V(sem): release the semaphore
Exit(i) ==
    /\ pc[i] = "exit"
    /\ sem' = 1
    /\ pc' = [pc EXCEPT ![i] = "ncs"]

Proc(i) == Request(i) \/ Enter(i) \/ LeaveCS(i) \/ Exit(i)

Next == \E i \in Procs : Proc(i)

Fairness ==
    \A i \in Procs :
        /\ SF_vars(Enter(i))
        /\ WF_vars(LeaveCS(i))
        /\ WF_vars(Exit(i))

Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
(* Properties *)

\* Safety: no two distinct processes are in the critical section at once
MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* Deadlock / livelock freedom: if some process is trying to enter,
\* eventually some process enters the critical section
DeadlockFreedom ==
    (\E i \in Procs : pc[i] = "enter") ~> (\E i \in Procs : pc[i] = "cs")

\* Starvation freedom: every process trying to enter eventually enters
StarvationFreedom ==
    \A i \in Procs : (pc[i] = "enter") ~> (pc[i] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => DeadlockFreedom /\ StarvationFreedom
=============================================================================