---------------------------- MODULE MutexQueue ----------------------------
(***************************************************************************)
(* Abstract model of an N-process mutual-exclusion protocol.               *)
(*                                                                         *)
(* Each process cycles through four control states:                       *)
(*   "ncs"  -> noncritical section                                         *)
(*   "try"  -> entry protocol (waiting to enter)                           *)
(*   "cs"   -> critical section                                            *)
(*   "exit" -> exit protocol                                               *)
(*                                                                         *)
(* The shared synchronization state is an abstract FIFO of requesters.     *)
(* A process may enter the critical section only when it is at the head    *)
(* of the queue. It stays at the head until it finishes its exit protocol. *)
(* This captures the required ordering without fixing an implementation.   *)
(*                                                                         *)
(* Fairness assumptions:                                                   *)
(*  - No fairness on Request(p): a process may stay in its noncritical     *)
(*    section forever.                                                     *)
(*  - Weak fairness on Enter(p), Exit(p), and Release(p) for every p.      *)
(*    A process in the critical section eventually leaves it and finishes  *)
(*    its exit protocol. A process that is continuously enabled to enter   *)
(*    eventually does so.                                                  *)
(*  With these assumptions, every process that tries eventually enters     *)
(*  the critical section (starvation freedom), so no deadlock occurs.      *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, Procs

ConstN     == 3
ConstProcs == 1..ConstN

ASSUME N \in Nat /\ N >= 1
ASSUME IsFiniteSet(Procs)

VARIABLES pc, queue

vars == <<pc, queue>>

States == {"ncs", "try", "cs", "exit"}

InQueue(p) == \E i \in 1..Len(queue) : queue[i] = p

TypeOK ==
  /\ pc \in [Procs -> States]
  /\ queue \in Seq(Procs)
  /\ Len(queue) <= Cardinality(Procs)

Init ==
  /\ pc = [p \in Procs |-> "ncs"]
  /\ queue = << >>

(* Leave the noncritical section and register the request. *)
Request(p) ==
  /\ pc[p] = "ncs"
  /\ pc' = [pc EXCEPT ![p] = "try"]
  /\ queue' = Append(queue, p)

(* Enter the critical section when it is your turn. *)
Enter(p) ==
  /\ pc[p] = "try"
  /\ queue # << >>
  /\ Head(queue) = p
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ UNCHANGED queue

(* Leave the critical section and begin the exit protocol. *)
Exit(p) ==
  /\ pc[p] = "cs"
  /\ pc' = [pc EXCEPT ![p] = "exit"]
  /\ UNCHANGED queue

(* Finish the exit protocol and release the turn. *)
Release(p) ==
  /\ pc[p] = "exit"
  /\ queue # << >>
  /\ Head(queue) = p
  /\ pc' = [pc EXCEPT ![p] = "ncs"]
  /\ queue' = Tail(queue)

ProcStep(p) == Request(p) \/ Enter(p) \/ Exit(p) \/ Release(p)

Next == \E p \in Procs : ProcStep(p)

Fairness ==
  \A p \in Procs :
     /\ WF_vars(Enter(p))
     /\ WF_vars(Exit(p))
     /\ WF_vars(Release(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety *)

MutualExclusion ==
  \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

QueueConsistent ==
  /\ \A p \in Procs : (pc[p] \in {"try", "cs", "exit"}) <=> InQueue(p)
  /\ \A i, j \in 1..Len(queue) : (i # j) => queue[i] # queue[j]
  /\ \A p \in Procs : (pc[p] \in {"cs", "exit"}) => (Head(queue) = p)

-----------------------------------------------------------------------------
(* Liveness *)

(* Starvation freedom: every process that tries eventually enters. *)
LivenessNaive ==
  \A p \in Procs : (pc[p] = "try") ~> (pc[p] = "cs")

(* Deadlock freedom: if some process is trying, some process eventually enters. *)
DeadlockFreedom ==
  (\E p \in Procs : pc[p] = "try") ~> (\E p \in Procs : pc[p] = "cs")

(* A process in the critical section eventually returns to noncritical work. *)
ExitProgress ==
  \A p \in Procs : (pc[p] = "cs") ~> (pc[p] = "ncs")

=============================================================================