---------------------------- MODULE GrowingSet ----------------------------
(***************************************************************************)
(* A minimal specification of a monotonically growing set.  The set starts *)
(* empty and at each step nondeterministically gains one element drawn     *)
(* from a fixed finite universe of data values.  Elements are never        *)
(* removed.                                                                *)
(***************************************************************************)

Data == {"d1", "d2"}

VARIABLE set

vars == <<set>>

TypeOK == set \subseteq Data

Init == set = {}

Add(d) == set' = set \cup {d}

Next == \E d \in Data : Add(d)

Spec == Init /\ [][Next]_vars

Monotonic == [][set \subseteq set']_vars

=============================================================================