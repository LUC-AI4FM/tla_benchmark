------------------------------- MODULE Peterson -------------------------------
EXTENDS Integers

(***************************************************************************)
(* Abstract lock specification, refined by Peterson's algorithm.           *)
(***************************************************************************)
---------------------------------- MODULE Lock ---------------------------------
CONSTANTS Procs, Free
VARIABLE owner

LockTypeOK == owner \in Procs \cup {Free}

LockInit == owner = Free

Acquire(p) == /\ owner = Free
              /\ owner' = p

Release(p) == /\ owner = p
              /\ owner' = Free

LockNext == \E p \in Procs : Acquire(p) \/ Release(p)

LockSpec == LockInit /\ [][LockNext]_owner

LockMutex == owner \in Procs \cup {Free}
================================================================================