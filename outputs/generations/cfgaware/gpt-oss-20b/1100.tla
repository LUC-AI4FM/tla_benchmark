------------------------------ MODULE MutualExclusion ------------------------------
EXTENDS Naturals, TLC

(* --algorithm MutualExclusion -------------------------------------------------
   This PlusCal algorithm models a simple mutual‑exclusion lock for two
   processes.  Each process cycles through the following locations:
     "nc"  – non‑critical section
     "l1"/"l2" – waiting to acquire the lock
     "cs"  – critical section

   The lock is represented by the variable `lockedBy`.  It is 0 when free,
   and equals the process number (1 or 2) when held.
--------------------------------------------------------------------------*)

(* --variables ---------------------------------------------------------------
   loc[i]   : current location of process i (i ∈ {1,2})
   lockedBy : owner of the lock (0 = free, 1 = proc 1, 2 = proc 2)
--------------------------------------------------------------------------*)
VARIABLES loc, lockedBy

LocSet == {"nc", "l1", "l2", "cs"}

(* --initial state ------------------------------------------------------------
   Both processes start in the non‑critical section and the lock is free. *)
Init ==
  /\ loc[1] = "nc"
  /\ loc[2] = "nc"
  /\ lockedBy = 0

(* --actions -----------------------------------------------------------------
   Non‑critical → waiting
   Waiting → critical (if lock free)
   Critical → non‑critical (release lock) *)
NonCriticalToWait1 ==
  /\ loc[1] = "nc"
  /\ loc' = [loc EXCEPT ![1] = "l1"]
  /\ UNCHANGED <<lockedBy>>

NonCriticalToWait2 ==
  /\ loc[2] = "nc"
  /\ loc' = [loc EXCEPT ![2] = "l2"]
  /\ UNCHANGED <<lockedBy>>

Acquire1 ==
  /\ loc[1] = "l1"
  /\ lockedBy = 0
  /\ loc' = [loc EXCEPT ![1] = "cs"]
  /\ lockedBy' = 1

Acquire2 ==
  /\ loc[2] = "l2"
  /\ lockedBy = 0
  /\ loc' = [loc EXCEPT ![2] = "cs"]
  /\ lockedBy' = 2

Release1 ==
  /\ loc[1] = "cs"
  /\ loc' = [loc EXCEPT ![1] = "nc"]
  /\ lockedBy' = 0

Release2 ==
  /\ loc[2] = "cs"
  /\ loc' = [loc EXCEPT ![2] = "nc"]
  /\ lockedBy' = 0

Next == 
  \/ NonCriticalToWait1
  \/ NonCriticalToWait2
  \/ Acquire1
  \/ Acquire2
  \/ Release1
  \/ Release2

(* --specification ------------------------------------------------------------
   The complete specification includes the initial condition, the next‑state
   relation, and a liveness property that guarantees progress from waiting to
   critical for process 1. *)
Liveness ==
  [] (loc[1] = "l1" => <> (loc[1] = "cs"))

Spec == Init /\ [][Next]_<<loc, lockedBy>> /\ Liveness

(* --type correctness ---------------------------------------------------------
   TypeOK ensures that all variables have the expected types. *)
TypeOK ==
  /\ loc ∈ [1..2 -> LocSet]
  /\ lockedBy ∈ {0,1,2}

(* --mutual‑exclusion invariant -----------------------------------------------
   LockInv states that at most one process can be in the critical section
   and that the lock variable is consistent with the location of the owner. *)
LockInv ==
  /\ (loc[1] = "cs" => lockedBy = 1)
  /\ (loc[2] = "cs" => lockedBy = 2)
  /\ (lockedBy = 0 => loc[1] # "cs" /\ loc[2] # "cs")
  /\ ~(loc[1] = "cs" /\ loc[2] = "cs")

=============================================================================