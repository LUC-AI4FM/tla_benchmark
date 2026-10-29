------------------------ MODULE AllocatorRefinement ------------------------
(***************************************************************************)
(* States that the scheduling allocator refines the simple allocator.      *)
(*                                                                         *)
(* The constants (Clients, Resources), the variables (unsat, alloc, sched) *)
(* and the definitions Init, Next, vars, the invariants and the            *)
(* specification Allocator (including its fairness conditions) all come    *)
(* from module SchedulingAllocator through EXTENDS. They are not           *)
(* redefined here, because redefining them would make SANY reject the      *)
(* module.                                                                 *)
(*                                                                         *)
(* The instance below substitutes, by name, the constants Clients and      *)
(* Resources and the variables unsat and alloc of SchedulingAllocator for  *)
(* the matching parameters of SimpleAllocator. The extra variable sched    *)
(* is hidden by the refinement.                                            *)
(***************************************************************************)
EXTENDS SchedulingAllocator

Simple == INSTANCE SimpleAllocator

SimpleAllocator == Simple!SimpleAllocator

THEOREM Allocator => SimpleAllocator
=============================================================================