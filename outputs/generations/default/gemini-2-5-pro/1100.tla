---- MODULE AbstractMutex ----
EXTENDS TLC, Integers

CONSTANT Procs
ASSUME Procs = {1, 2}

VARIABLES lock, pc

vars == <<lock, pc>>

(* The set of process locations. *)
Locations == {"ncs", "l1", "cs"}

(*
--algorithm AbstractMutex
{
  variables lock = "free";
  process (p \in Procs)
  {
ncs:
    while (TRUE) {
l1:   await lock = "free";
      lock := self;
cs:   skip; \* Critical section
      lock := "free";
    }
  }
}
*)

(* Type invariant: variables have the correct values. *)
TypeOK ==
    /\ lock \in {"free"} \cup Procs
    /\ pc \in [Procs -> Locations]

(* Initial state of the system. *)
Init ==
    /\ lock = "free"
    /\ pc = [p \in Procs |-> "ncs"]

(* Process p moves from non-critical to waiting. This corresponds to the
   implicit transition before the 'await' in the PlusCal algorithm. *)
TryToAcquire(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "l1"]
    /\ UNCHANGED lock

(* If the lock is free, process p acquires it and enters the critical section. *)
Acquire(p) ==
    /\ pc[p] = "l1"
    /\ lock = "free"
    /\ lock' = p
    /\ pc' = [pc EXCEPT ![p] = "cs"]

(* Process p leaves the critical section and releases the lock. *)
Release(p) ==
    /\ pc[p] = "cs"
    /\ lock' = "free"
    /\ pc' = [pc EXCEPT ![p] = "ncs"]

(* An action for a single process p. *)
ProcessAction(p) ==
    \/ TryToAcquire(p)
    \/ Acquire(p)
    \/ Release(p)

(* The next-state relation is the disjunction of all possible process actions. *)
Next == \E p \in Procs: ProcessAction(p)

(* Fairness condition: each process is weakly fair. This means if a process
   can take a step, it eventually will. This is needed to prove liveness. *)
Fairness == \A p \in Procs: WF_vars(ProcessAction(p))

(* The full specification including safety and fairness. *)
Spec == Init /\ [][Next]_vars /\ Fairness

(* -- SAFETY INVARIANTS -- *)

(* Mutual exclusion: at most one process is in the critical section at a time. *)
MutualExclusion ==
    Cardinality({p \in Procs : pc[p] = "cs"}) <= 1

(* -- LIVENESS PROPERTY -- *)

(* If process 1 is waiting for the lock, it eventually enters the critical section. *)
Liveness == pc[1] = "l1" ~> pc[1] = "cs"

=============================================================================