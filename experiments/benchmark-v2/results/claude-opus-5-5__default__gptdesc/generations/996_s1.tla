----------------------- MODULE AllocatorRefinement -----------------------
(***************************************************************************)
(* Refinement relationship between two allocator specifications.           *)
(* The scheduling allocator, with its fairness conditions, implements the  *)
(* simple allocator.                                                       *)
(*                                                                         *)
(* This module EXTENDS SchedulingAllocator. That module supplies the       *)
(* CONSTANTS Clients and Resources. It also supplies the VARIABLES         *)
(* unsat, alloc, pool and sched. Its Init and Next definitions and its     *)
(* complete specification Allocator also come from there. Allocator is     *)
(* Init /\ [][Next]_vars plus fairness, and it serves as this module's     *)
(* Spec.                                                                   *)
(*                                                                         *)
(* SimpleAllocator is instantiated with an identity substitution. Each of  *)
(* its constants and variables is matched with the identically named      *)
(* symbol in this module.                                                  *)
(***************************************************************************)
EXTENDS SchedulingAllocator

Simple == INSTANCE SimpleAllocator

SimpleAllocator == Simple!SimpleAllocator

THEOREM Allocator => SimpleAllocator
==========================================================================