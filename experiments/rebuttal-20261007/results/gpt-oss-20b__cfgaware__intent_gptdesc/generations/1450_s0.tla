------------------------------ MODULE RandomSubset ------------------------------
EXTENDS Naturals

CONSTANTS n, m, k

DOMAIN    == 1..n
CODOMAIN  == 1..m
Universe  == { f \in [DOMAIN -> CODOMAIN] }

VARIABLES S

(* ------------------------------------------------------------------ *)
(* Initial state: uniformly choose any k‑element subset of the universe. *)
Init ==
    /\ S ⊆ Universe
    /\ #S = k

(* ------------------------------------------------------------------ *)
(* After initialization, the chosen subset is immutable. *)
Next ==
    /\ S' = S

Spec == Init /\ [] Next

(* ------------------------------------------------------------------ *)
(* Invariant: the subset always remains a k‑element set of total functions. *)
Invariant ==
    /\ S ⊆ Universe
    /\ #S = k

THEOREM Spec => [] Invariant
=============================================================================