------------------------ MODULE AllocatorRefinement ------------------------
(***************************************************************************)
(* States a refinement relationship between two allocator specifications. *)
(* The constants, variables, Init, Next, the fairness conditions and the   *)
(* complete specification Allocator are inherited from the module          *)
(* SchedulingAllocator. They are not redeclared here because redefining    *)
(* them would cause multiple-definition errors in SANY.                    *)
(*                                                                         *)
(* The module SimpleAllocator is instantiated as Simple. Each of its       *)
(* constants and variables is substituted implicitly by the identically    *)
(* named constant or variable of SchedulingAllocator: Clients, Resources,  *)
(* unsat and alloc.                                                        *)
(***************************************************************************)
EXTENDS SchedulingAllocator

Simple == INSTANCE SimpleAllocator

SimpleAllocator == Simple!SimpleAllocator

(***************************************************************************)
(* Refinement: every behavior of the scheduling allocator, including its   *)
(* fairness conditions, is a behavior of the simple allocator.             *)
(***************************************************************************)
THEOREM Allocator => SimpleAllocator
=============================================================================