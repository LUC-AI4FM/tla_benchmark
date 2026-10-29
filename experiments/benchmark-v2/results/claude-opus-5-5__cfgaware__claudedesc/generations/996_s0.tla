------------------------ MODULE AllocatorRefinement ------------------------
(***************************************************************************)
(* The scheduling allocator is a refinement of the simple allocator.       *)
(* Constants Clients and Resources, the state variables, and the           *)
(* specification Allocator are inherited from module SchedulingAllocator.  *)
(***************************************************************************)
EXTENDS SchedulingAllocator

(***************************************************************************)
(* Instantiate the simple allocator.  Its constants (Clients, Resources)   *)
(* and variables (unsat, alloc) are mapped implicitly to the identically   *)
(* named constants and variables of the scheduling allocator.              *)
(***************************************************************************)
Simple == INSTANCE SimpleAllocator

SimpleAllocator == Simple!SimpleAllocator

THEOREM Allocator => SimpleAllocator
=============================================================================