--------------------------- MODULE MCSession9onebit ---------------------------
(***************************************************************************)
(* Model-checking wrapper for the one-bit mutual exclusion algorithm.      *)
(* The algorithm (Init, Next, Spec, vars, pc, ...) is defined in the       *)
(* imported module Session9onebit.  This module only fixes concrete model  *)
(* constants and states the safety and liveness properties to be checked.  *)
(***************************************************************************)
EXTENDS Session9onebit

(***************************************************************************)
(* Concrete model constants: three processes.                             *)
(***************************************************************************)
ConstN     == 3
ConstProcs == 0 .. (ConstN - 1)

(***************************************************************************)
(* Model entry points (the algorithm's Init, Next and Spec are imported    *)
(* from Session9onebit and cannot be redefined here).                      *)
(***************************************************************************)
MCInit == Init
MCNext == Next
MCSpec == Spec

(***************************************************************************)
(* Helper predicates over the imported program counter pc.                 *)
(***************************************************************************)
InCS(i)   == pc[i] = "cs"
Trying(i) == pc[i] \notin {"ncs", "cs"}

(***************************************************************************)
(* Safety: no two distinct processes are in the critical section at once.  *)
(***************************************************************************)
MutualExclusion ==
    \A i, j \in ConstProcs : (i # j) => ~(InCS(i) /\ InCS(j))

(***************************************************************************)
(* Deadlock / livelock freedom: if some process is trying to enter, then   *)
(* eventually some process enters the critical section.                    *)
(***************************************************************************)
DeadlockFree ==
    (\E i \in ConstProcs : Trying(i)) ~> (\E i \in ConstProcs : InCS(i))

(***************************************************************************)
(* Starvation freedom for process 0: if process 0 is trying, it            *)
(* eventually enters its critical section.                                 *)
(***************************************************************************)
NoStarveProc0 == Trying(0) ~> InCS(0)

(***************************************************************************)
(* Starvation freedom for process 1.                                       *)
(* NOTE: NoStarveProc1 is NOT satisfied by the one-bit algorithm; the      *)
(* model checker is expected to report a counterexample for it.            *)
(***************************************************************************)
NoStarveProc1 == Trying(1) ~> InCS(1)

=============================================================================