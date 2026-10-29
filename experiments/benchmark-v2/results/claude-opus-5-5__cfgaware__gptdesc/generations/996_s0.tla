------------------------ MODULE AllocatorRefinement ------------------------
(***************************************************************************)
(* The scheduling allocator is a refinement of the simple allocator.       *)
(* Clients, Resources and Allocator come from SchedulingAllocator.         *)
(***************************************************************************)
EXTENDS SchedulingAllocator

Simple == INSTANCE SimpleAllocator

SimpleAllocator == Simple!SimpleAllocator

THEOREM Allocator => SimpleAllocator
=============================================================================