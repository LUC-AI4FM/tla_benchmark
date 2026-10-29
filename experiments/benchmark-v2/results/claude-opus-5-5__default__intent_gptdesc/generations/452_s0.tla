------------------------------ MODULE CyclicCounter ------------------------------
(***************************************************************************)
(* A simple cyclic counter that evolves modulo a fixed positive modulus N. *)
(* The counter starts at 0; the only step increments it by one and reduces *)
(* the result modulo N, so the value always stays within 0..N-1.           *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N            \* the modulus, a positive integer

ASSUME NAssumption == N \in Nat /\ N > 0

VARIABLE counter

vars == <<counter>>

(***************************************************************************)
(* State space: the set of residues modulo N.                              *)
(***************************************************************************)
Residues == 0 .. (N - 1)

TypeOK == counter \in Residues

(***************************************************************************)
(* Initial predicate.                                                      *)
(***************************************************************************)
Init == counter = 0

(***************************************************************************)
(* The single kind of step: increment by one, then reduce modulo N.        *)
(***************************************************************************)
Increment == counter' = (counter + 1) % N

(***************************************************************************)
(* Next-state relation. Stuttering steps (counter' = counter) are not part *)
(* of Next except in the degenerate case N = 1, where incrementing modulo  *)
(* 1 necessarily yields 0 again. In the specification, stuttering steps    *)
(* are allowed only through the standard [Next]_vars form, as TLA+ needs   *)
(* for stuttering invariance. Weak fairness on Next forces real progress.  *)
(***************************************************************************)
Next == Increment

(***************************************************************************)
(* Full specification. Every behavior starts in Init, and every step is    *)
(* either an Increment step or a stuttering step. Weak fairness ensures    *)
(* that the increment is taken infinitely often, which gives infinite      *)
(* execution where the step is repeated forever.                           *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Safety properties.                                                      *)
(***************************************************************************)

\* The counter is always an integer within 0..N-1.
RangeInvariant == counter \in Nat /\ 0 <= counter /\ counter <= N - 1

Safety == []RangeInvariant

\* Every step that changes the state follows the increment-modulo relation.
StepConformance == [][counter' = (counter + 1) % N]_vars

\* All behaviors start from the given initialization.
InitProperty == Init

(***************************************************************************)
(* Liveness properties.                                                    *)
(***************************************************************************)

\* The increment step is taken infinitely often (non-terminating execution),
\* when it actually changes the state (N > 1).
InfiniteProgress == (N > 1) => []<><<Next>>_vars

\* From any reachable state, every residue in 0..N-1 is eventually visited.
\* Because this holds at every point, the counter cycles through all
\* residues infinitely often.
VisitsAllResidues == \A v \in Residues : []<>(counter = v)

\* An equivalent "from any state, eventually reach v" formulation.
EventuallyReachEach == \A v \in Residues : TRUE ~> (counter = v)

(***************************************************************************)
(* Theorems stating that the specification satisfies its properties.       *)
(***************************************************************************)
THEOREM Spec => []TypeOK
THEOREM Spec => Safety
THEOREM Spec => StepConformance
THEOREM Spec => InitProperty
THEOREM Spec => InfiniteProgress
THEOREM Spec => VisitsAllResidues
THEOREM Spec => EventuallyReachEach
=============================================================================