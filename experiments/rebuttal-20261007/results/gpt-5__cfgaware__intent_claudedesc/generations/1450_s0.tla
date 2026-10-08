------------------------------ MODULE RandomSubsetFunctionSampling ------------------------------

EXTENDS Naturals, TLC

(*
This module demonstrates using RandomSubset to sample from a massive function set
[Domain -> Codomain] without enumerating it. The only correctness property is a
trivially true invariant, since the goal is to exercise RandomSubset at scale.
*)

(***************************************************************************)
(* Basic parameters for the huge function space                            *)
(***************************************************************************)

Domain   == 1..9
Codomain == 0..9

D == Domain
C == Codomain

Funcs == [D -> C]

(*
There are |C|^|D| = 10^9 total functions, which is astronomically large.
We will sample approximately one thousand of them.
*)
K == 1000
SampleSize == K

(***************************************************************************)
(* State variable                                                          *)
(***************************************************************************)

VARIABLES Sample

(***************************************************************************)
(* Initialization and transition                                           *)
(***************************************************************************)

Init ==
  /\ Sample = RandomSubset(Funcs, SampleSize)

Next ==
  UNCHANGED Sample

Spec ==
  Init /\ [][Next]_<<Sample>>

(***************************************************************************)
(* Trivial invariant                                                       *)
(***************************************************************************)

Inv == TRUE
TriviallyTrue == TRUE
AlwaysTrue == TRUE

============================================================================