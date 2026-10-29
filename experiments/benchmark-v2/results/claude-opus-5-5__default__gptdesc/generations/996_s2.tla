------------------------ MODULE AllocatorRefinement -------------------------
(***************************************************************************)
(* Refinement of the simple allocator by the scheduling allocator.        *)
(* The constants (Clients, Resources), the variables (unsat, alloc,       *)
(* sched), Init, Next, the invariants, the fairness conditions and the    *)
(* specification Allocator all come from SchedulingAllocator.             *)
(***************************************************************************)
EXTENDS SchedulingAllocator

(***************************************************************************)
(* Instantiate SimpleAllocator. Its constants Clients and Resources and   *)
(* its variables unsat and alloc are substituted implicitly by the        *)
(* identically named constants and variables of SchedulingAllocator.      *)
(***************************************************************************)
Simple == INSTANCE SimpleAllocator

SimpleAllocator == Simple!SimpleAllocator

(***************************************************************************)
(* The specification of this module is the scheduling allocator.          *)
(***************************************************************************)
Spec == Allocator

(***************************************************************************)
(* The scheduling allocator refines the simple allocator.                 *)
(***************************************************************************)
THEOREM Allocator => SimpleAllocator
=============================================================================