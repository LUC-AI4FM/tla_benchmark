------------------------------ MODULE MutualExclusion ------------------------------
EXTENDS Integers, TLC

CONSTANTS Proc

VARIABLES pc, lock

vars == <<pc, lock>>

Procs == {1, 2}

Init == 
    /\ pc = [p \in Procs |-> "ncs"]
    /\ lock = 0

TypeOK ==
    /\ pc \in [Procs -> {"ncs", "l1", "cs"}]
    /\ lock \in {0, 1, 2}

MutualExclusion ==
    ~(pc[1] = "cs" /\ pc[2] = "cs")

(* Process actions *)

(* Process p moves from non-critical section to waiting location l1 *)
EnterWait(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "l1"]
    /\ UNCHANGED lock

(* Process p acquires the lock when it is free and enters critical section *)
AcquireLock(p) ==
    /\ pc[p] = "l1"
    /\ lock = 0
    /\ lock' = p
    /\ pc' = [pc EXCEPT ![p] = "cs"]

(* Process p releases the lock and returns to non-critical section *)
ReleaseLock(p) ==
    /\ pc[p] = "cs"
    /\ lock = p
    /\ lock' = 0
    /\ pc' = [pc EXCEPT ![p] = "ncs"]

(* Next state relation *)
proc(p) == EnterWait(p) \/ AcquireLock(p) \/ ReleaseLock(p)

Next == \E p \in Procs : proc(p)

(* Fairness conditions - weak fairness for all process actions *)
Fairness == \A p \in Procs : WF_vars(proc(p))

(* Specification with fairness *)
Spec == Init /\ [][Next]_vars /\ Fairness

(* Liveness property: process 1 at l1 leads to eventually reaching cs *)
Liveness == pc[1] = "l1" ~> pc[1] = "cs"

===================================================================================