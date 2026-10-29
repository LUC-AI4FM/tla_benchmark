---------------------------- MODULE MCSession9onebit ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the one-bit mutual exclusion algorithm.     *)
(* The operational algorithm (CONSTANTS N and Procs, the variable pc and   *)
(* any other variables, and Init, Next and Spec with their fairness        *)
(* conditions) is defined in module Session9onebit, imported by EXTENDS.   *)
(* This module only fixes concrete model values for the constants and      *)
(* states the safety and liveness properties to be checked.                *)
(*                                                                         *)
(* In the TLC model configuration:                                         *)
(*   CONSTANT N <- ConstN                                                  *)
(*   CONSTANT Procs <- ConstProcs                                          *)
(*   SPECIFICATION Spec                                                    *)
(*   INVARIANT MutualExclusion                                             *)
(*   PROPERTIES NoDeadlock NoStarveProc0 NoStarveProc1                     *)
(***************************************************************************)
EXTENDS Session9onebit, Naturals, TLC

(***************************************************************************)
(* Concrete model constants: three processes, numbered 0, 1 and 2.         *)
(***************************************************************************)
ConstN == 3

ConstProcs == 0 .. (ConstN - 1)

(***************************************************************************)
(* Helper predicates over the imported program-counter variable pc.        *)
(***************************************************************************)
InCS(i) == pc[i] = "cs"

(* A process is trying when it is neither in its noncritical section nor *)
(* in its critical section.                                                *)
Trying(i) == pc[i] \notin {"ncs", "cs"}

(***************************************************************************)
(* Safety: no two distinct processes are in the critical section at the    *)
(* same time.                                                              *)
(***************************************************************************)
MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(InCS(i) /\ InCS(j))

(***************************************************************************)
(* Liveness: deadlock and livelock freedom. If some process is trying to   *)
(* enter the critical section, then some process eventually enters it.     *)
(***************************************************************************)
NoDeadlock ==
    (\E i \in Procs : Trying(i)) ~> (\E i \in Procs : InCS(i))

(***************************************************************************)
(* Liveness: starvation freedom for process 0. Whenever process 0 is       *)
(* trying to enter, it eventually reaches the critical section.            *)
(***************************************************************************)
NoStarveProc0 ==
    Trying(0) ~> InCS(0)

(***************************************************************************)
(* Liveness: starvation freedom for process 1.                             *)
(* NOTE: NoStarveProc1 is NOT satisfied by the one-bit algorithm; TLC is   *)
(* expected to report a counterexample in which process 1 starves.         *)
(***************************************************************************)
NoStarveProc1 ==
    Trying(1) ~> InCS(1)

=============================================================================