------------------------ MODULE AllocatorRefinement ------------------------
(***************************************************************************)
(* The scheduling allocator is a refinement of the simple allocator.       *)
(* SchedulingAllocator supplies the constants Clients and Resources, the   *)
(* variables (unsat, alloc, sched), Init, Next and the full specification  *)
(* Allocator, including its fairness conditions.                           *)
(***************************************************************************)
EXTENDS SchedulingAllocator

\* Map the scheduling allocator's state onto the simple allocator.
\* Clients, Resources, unsat and alloc are substituted by the identically
\* named symbols inherited from SchedulingAllocator.
Simple == INSTANCE SimpleAllocator

\* The simple allocator's specification, including its safety and liveness.
SimpleAllocator == Simple!SimpleAllocator

\* The refinement claim: every behavior of the scheduling allocator is
\* also a behavior of the simple allocator.
THEOREM Allocator => SimpleAllocator

(***************************************************************************)
(* Model-checking configuration (AllocatorRefinement.cfg):                 *)
(*                                                                         *)
(*   CONSTANTS                                                             *)
(*     Clients = {c1, c2, c3}                                              *)
(*     Resources = {r1, r2}                                                *)
(*   SPECIFICATION Allocator                                               *)
(*   PROPERTY SimpleAllocator                                              *)
(***************************************************************************)
=============================================================================