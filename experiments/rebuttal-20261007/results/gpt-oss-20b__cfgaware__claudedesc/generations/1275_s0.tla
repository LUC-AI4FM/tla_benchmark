------------------------------ MODULE NegInit ------------------------------
EXTENDS Integers

VARIABLES s

(* Initialization predicate parameterized by a variable *)
Init(var) == ∃ v \in \{0,1\} : (var = v /\ v < 1)

(* Next-state relation: stuttering only *)
Next == (s' = s)

Spec == Init(s) /\ [][Next]_{\{s\}}

Inv == (s < 1)

=============================================================================