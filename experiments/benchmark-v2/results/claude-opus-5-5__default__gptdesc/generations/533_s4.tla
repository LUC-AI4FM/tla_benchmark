------------------------------- MODULE MCSession4 -------------------------------
(***************************************************************************)
(* Model-checking helper module for Session4.  It only defines two        *)
(* constant-valued operators that are meant to be substituted for the     *)
(* constants of Session4 when running TLC:                                 *)
(*                                                                         *)
(*   - const_minValue : a distinguished minimum integer value              *)
(*   - const_Input    : a finite set of tuples.  For each l in 0..5 it     *)
(*                      contains every function from 1..l into the         *)
(*                      shifted range (l+1)..(2*l).                         *)
(*                                                                         *)
(* There are no variables, actions, temporal formulas, or invariants of    *)
(* its own.  It is purely a set of top-level mathematical definitions.     *)
(***************************************************************************)
EXTENDS Session4, Integers, TLC

\* Distinguished minimum integer value, used in place of minus infinity.
const_minValue == -1000

\* Union of function sets: for each l in 0..5, all tuples of length l
\* whose entries lie in (l+1)..(2*l).
const_Input == UNION { [1..l -> (l+1)..(2*l)] : l \in 0..5 }

=============================================================================