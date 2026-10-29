---------------------------- MODULE MCSession9sem ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the Session9sem semaphore-based mutual      *)
(* exclusion protocol. It fixes the number of processes to 3, defines the  *)
(* process set as 0..(ConstN-1), asserts mutual exclusion as a safety      *)
(* property, and states deadlock/livelock freedom and starvation freedom   *)
(* as leads-to liveness properties over the control-state variable pc.     *)
(*                                                                         *)
(* The Session9sem protocol is included inline so that this module parses  *)
(* on its own.                                                             *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

(***************************************************************************)
(* Concrete constants for model checking                                  *)
(***************************************************************************)
ConstN    == 3
ConstProc == 0..(ConstN - 1)

N    == ConstN
Proc == ConstProc

(***************************************************************************)
(* Session9sem: binary-semaphore mutual exclusion                         *)
(***************************************************************************)
VARIABLES pc, sem

vars == << pc, sem >>

PCValues == {"ncs", "wait", "cs"}

TypeOK ==
    /\ pc  \in [Proc -> PCValues]
    /\ sem \in {0, 1}

Init ==
    /\ pc  = [p \in Proc |-> "ncs"]
    /\ sem = 1

\* Leave the non-critical section and request the critical section.
Request(p) ==
    /\ pc[p] = "ncs"
    /\ pc'   = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED sem

\* P(sem): acquire the semaphore and enter the critical section.
Enter(p) ==
    /\ pc[p] = "wait"
    /\ sem   = 1
    /\ sem'  = 0
    /\ pc'   = [pc EXCEPT ![p] = "cs"]

\* V(sem): release the semaphore and return to the non-critical section.
Exit(p) ==
    /\ pc[p] = "cs"
    /\ sem'  = 1
    /\ pc'   = [pc EXCEPT ![p] = "ncs"]

Next == \E p \in Proc : Request(p) \/ Enter(p) \/ Exit(p)

\* A process may stay in its non-critical section forever (no fairness on
\* Request). It must eventually leave the critical section (weak fairness on
\* Exit). A waiting process that is repeatedly able to acquire the semaphore
\* eventually does so (strong fairness on Enter).
Fairness ==
    /\ \A p \in Proc : WF_vars(Exit(p))
    /\ \A p \in Proc : SF_vars(Enter(p))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety                                                                  *)
(***************************************************************************)
MutualExclusion ==
    \A i, j \in Proc : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

(***************************************************************************)
(* Liveness                                                                *)
(***************************************************************************)
\* Deadlock/livelock freedom: if some process is waiting, then some process
\* eventually enters the critical section.
DeadlockFree ==
    (\E p \in Proc : pc[p] = "wait") ~> (\E p \in Proc : pc[p] = "cs")

\* Starvation freedom: every waiting process eventually enters the critical
\* section.
StarvationFree ==
    \A p \in Proc : (pc[p] = "wait") ~> (pc[p] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => DeadlockFree /\ StarvationFree
=============================================================================