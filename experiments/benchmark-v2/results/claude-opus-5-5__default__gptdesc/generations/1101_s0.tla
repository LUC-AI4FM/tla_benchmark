------------------------------- MODULE Peterson -------------------------------
(***************************************************************************)
(* Peterson's mutual exclusion algorithm for two processes.                *)
(***************************************************************************)
EXTENDS Naturals

(***************************************************************************)
(* Abstract lock specification, used as the target of the refinement.     *)
(***************************************************************************)
---------------------------------- MODULE Lock ---------------------------------
CONSTANT Procs
VARIABLE lockpc

LInit == lockpc = [p \in Procs |-> "a0"]

Enter(p) == /\ lockpc[p] = "a0"
            /\ \A q \in Procs : lockpc[q] # "cs"
            /\ lockpc' = [lockpc EXCEPT ![p] = "cs"]

Exit(p) == /\ lockpc[p] = "cs"
           /\ lockpc' = [lockpc EXCEPT ![p] = "a0"]

LNext == \E p \in Procs : Enter(p) \/ Exit(p)

LSpec == LInit /\ [][LNext]_lockpc

LMutex == \A p, q \in Procs : (lockpc[p] = "cs" /\ lockpc[q] = "cs") => p = q
================================================================================