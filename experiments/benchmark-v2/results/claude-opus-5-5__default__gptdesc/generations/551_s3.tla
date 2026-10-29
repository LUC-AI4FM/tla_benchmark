---------------------------- MODULE MCSession9onebit ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the one-bit mutual exclusion algorithm.      *)
(* The algorithm (variables, Init, Next, Spec) is defined in               *)
(* Session9onebit and imported here via EXTENDS. This module only fixes   *)
(* the model constants and states the properties to be checked over the    *)
(* imported state variable pc.                                             *)
(***************************************************************************)
EXTENDS Session9onebit

(***************************************************************************)
(* Concrete model constants: three processes, identified as 0, 1 and 2.    *)
(* In the TLC configuration these are substituted for the constants of     *)
(* Session9onebit, e.g.  N <- ConstN,  Procs <- ConstProcs.                *)
(***************************************************************************)
ConstN == 3

ConstProcs == 0 .. (ConstN - 1)

(***************************************************************************)
(* Auxiliary predicates on the imported variable pc.                       *)
(***************************************************************************)
InCS(p)   == pc[p] = "cs"

Trying(p) == pc[p] \notin {"ncs", "cs"}

(***************************************************************************)
(* Safety: no two distinct processes are in the critical section at once.  *)
(***************************************************************************)
MutualExclusion ==
    \A p, q \in ConstProcs : (p # q) => ~(InCS(p) /\ InCS(q))

(***************************************************************************)
(* Deadlock / livelock freedom: if some process is trying to enter the     *)
(* critical section, then eventually some process enters it.               *)
(***************************************************************************)
DeadlockFree ==
    (\E p \in ConstProcs : Trying(p)) ~> (\E p \in ConstProcs : InCS(p))

(***************************************************************************)
(* Starvation freedom for individual processes.                            *)
(***************************************************************************)
NoStarveProc0 == Trying(0) ~> InCS(0)

\* Note: NoStarveProc1 is NOT satisfied by the one-bit algorithm;
\* TLC is expected to report a counterexample for this property.
NoStarveProc1 == Trying(1) ~> InCS(1)

(***************************************************************************)
(* Theorems to be checked by TLC against the imported specification Spec. *)
(***************************************************************************)
THEOREM Spec => []MutualExclusion
THEOREM Spec => DeadlockFree
THEOREM Spec => NoStarveProc0
=============================================================================