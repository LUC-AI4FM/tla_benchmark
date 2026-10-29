---------------------- MODULE AllocatorRefinement ----------------------
(*************************************************************************)
(* Refinement of the simple allocator by the scheduling allocator.       *)
(* The scheduling allocator's variables unsat and alloc are used         *)
(* directly as the refinement mapping for the simple allocator's         *)
(* variables of the same names.                                          *)
(*************************************************************************)
EXTENDS SchedulingAllocator

Simple == INSTANCE SimpleAllocator

SimpleAllocator == Simple!SimpleAllocator

THEOREM Allocator => SimpleAllocator
=============================================================================