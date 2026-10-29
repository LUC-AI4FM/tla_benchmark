---------------------------- MODULE MutexCounter ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ConstN == N \in Nat /\ N >= 1

ASSUME ConstN

Procs == 1..N

PCStates == {"ncs", "e1", "e2", "cs", "Done"}

(* Shared state:  x    -- shared counter                                    *)
(*                lock -- 0 = free, 1 = held                                 *)
(* Local state:   pc   -- control location of each process                  *)
(*                t    -- local copy of the counter read inside the CS       *)
VARIABLES x, lock, pc, t

vars == << x, lock, pc, t >>

InCS(i) == pc[i] \in {"e2", "cs"}

-----------------------------------------------------------------------------

Init == /\ x = 0
        /\ lock = 0
        /\ pc = [i \in Procs |-> "ncs"]
        /\ t = [i \in Procs |-> 0]

(* Leave the noncritical region and start the entry protocol *)
NCS(i) == /\ pc[i] = "ncs"
          /\ pc' = [pc EXCEPT ![i] = "e1"]
          /\ UNCHANGED << x, lock, t >>

(* Entry step 1: wait for the lock to be free and acquire it *)
E1(i) == /\ pc[i] = "e1"
         /\ lock = 0
         /\ lock' = 1
         /\ pc' = [pc EXCEPT ![i] = "e2"]
         /\ UNCHANGED << x, t >>

(* Entry step 2: read the shared counter into the local variable *)
E2(i) == /\ pc[i] = "e2"
         /\ t' = [t EXCEPT ![i] = x]
         /\ pc' = [pc EXCEPT ![i] = "cs"]
         /\ UNCHANGED << x, lock >>

(* Critical section: write back incremented counter, release lock, finish *)
CS(i) == /\ pc[i] = "cs"
         /\ x' = t[i] + 1
         /\ lock' = 0
         /\ pc' = [pc EXCEPT ![i] = "Done"]
         /\ UNCHANGED t

Proc(i) == NCS(i) \/ E1(i) \/ E2(i) \/ CS(i)

Terminating == /\ \A i \in Procs : pc[i] = "Done"
               /\ UNCHANGED vars

Next == (\E i \in Procs : Proc(i)) \/ Terminating

Fairness == \A i \in Procs : WF_vars(Proc(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Invariants *)

TypeOK == /\ x \in 0..N
          /\ lock \in {0, 1}
          /\ pc \in [Procs -> PCStates]
          /\ t \in [Procs -> 0..N]

CriticalSecInv == \A i, j \in Procs : (i # j) => ~(InCS(i) /\ InCS(j))

AddCorrect == (\A i \in Procs : pc[i] = "Done") => (x = N)

CounterRange == x \in 0..N

LockConsistent == (lock = 1) <=> (\E i \in Procs : InCS(i))

-----------------------------------------------------------------------------
(* Liveness properties *)

Progress == \A i \in Procs :
              (pc[i] \in {"e1", "e2"}) ~> (pc[i] = "cs" \/ pc[i] = "Done")

ProcTermination == \A i \in Procs : <>(pc[i] = "Done")

Termination == <>(\A i \in Procs : pc[i] = "Done")

=============================================================================