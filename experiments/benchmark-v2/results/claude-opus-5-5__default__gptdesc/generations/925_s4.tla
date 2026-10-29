---------------------------- MODULE MCInnerFIFO ----------------------------
(***************************************************************************)
(* This module adds a TLC-specific state constraint for model checking the *)
(* inner FIFO specification without modifying the InnerFIFO module itself. *)
(*                                                                         *)
(* The InnerFIFO specification has an unbounded state space: the queue q   *)
(* can grow arbitrarily large. To allow TLC to explore a finite set of     *)
(* states, this module introduces a constant bound qLen and a predicate    *)
(* qConstraint that limits the length of q to at most qLen.                *)
(*                                                                         *)
(* This module does not define the FIFO algorithm, any actions, or any     *)
(* temporal properties. Init, Next, Spec and the type invariant are all    *)
(* inherited from InnerFIFO. The TLC configuration file should name        *)
(* qConstraint as a CONSTRAINT, for example:                               *)
(*                                                                         *)
(*    CONSTANTS Message = {m1, m2}                                         *)
(*              qLen    = 2                                                *)
(*    SPECIFICATION Spec                                                   *)
(*    CONSTRAINT    qConstraint                                            *)
(*    INVARIANT     TypeInvariant                                          *)
(***************************************************************************)
EXTENDS InnerFIFO

CONSTANT qLen   \* Upper bound on the length of the queue q

ASSUME qLen \in Nat

qConstraint == Len(q) \leq qLen

=============================================================================