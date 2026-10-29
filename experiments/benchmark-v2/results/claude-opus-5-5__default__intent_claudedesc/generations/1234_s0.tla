---------------------------- MODULE ModCounter ----------------------------
(***************************************************************************)
(* A simple cyclic counter that starts at zero and increments by one on    *)
(* each step, wrapping around to zero after reaching its maximum value     *)
(* N - 1. The intended instantiation is N = 5, which gives a modulo-5      *)
(* counter ranging over 0..4.                                              *)
(*                                                                         *)
(* The modulus is a CONSTANT so that other modules can instantiate this    *)
(* counter with different parameters, e.g.                                 *)
(*     C5 == INSTANCE ModCounter WITH N <- 5, x <- c5                      *)
(* or compose several counters together.                                   *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N          \* The modulus; the counter ranges over 0..N-1 (N = 5)

ASSUME NAssumption == N \in Nat /\ N > 0

VARIABLE x          \* The current counter value

vars == <<x>>

Range == 0 .. (N - 1)

-----------------------------------------------------------------------------
(* Initial state: the counter begins at zero. *)
Init == x = 0

(* Counting step: advance to the next value, wrapping from N-1 to 0. *)
Increment == x' = (x + 1) % N

Next == Increment

(* Stuttering steps (x' = x) are permitted by [Next]_vars. *)
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety: the counter value always stays within 0..N-1 (0..4 for N=5). *)
TypeOK == x \in Range

RangeInvariant == x \in Nat /\ x >= 0 /\ x <= N - 1

(* Determinism: whenever the state changes, it moves to the unique *)
(* successor value (x + 1) % N.                                    *)
DeterministicProgression == [][x' = (x + 1) % N]_vars

(* Wraparound: from the maximum value, the only change is back to 0. *)
Wraparound == [][(x = N - 1) => (x' = 0)]_vars

(* Theorems stating the properties hold for the specification. *)
THEOREM Spec => []TypeOK
THEOREM Spec => []RangeInvariant
THEOREM Spec => DeterministicProgression
THEOREM Spec => Wraparound
=============================================================================