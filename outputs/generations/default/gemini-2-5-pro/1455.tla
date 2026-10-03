---- MODULE SubsetProperties ----
EXTENDS Integers, Naturals

VARIABLES b

(*
--algorithm trivial_subset_checker
begin
  b := TRUE;
  while TRUE do
    b := (SUBSET (1..2) \subseteq SUBSET (1..3))
      /\ (~(SUBSET (1..3) \subseteq SUBSET (1..2)))
      /\ (SUBSET {"a", "b"} \subseteq SUBSET {"a", "b", "c"})
      /\ (~(SUBSET {"a", "c"} \subseteq SUBSET {"a", "b"}))
      /\ (SUBSET Nat \subseteq SUBSET Int)
      /\ (~(SUBSET Int \subseteq SUBSET Nat));
  end while;
end algorithm;
*)

Invariant ==
    /\ b = TRUE
    /\ b \in BOOLEAN

Init == b = TRUE

Next ==
    b' = (
        /\ SUBSET (1..2) \subseteq SUBSET (1..3)
        /\ ~(SUBSET (1..3) \subseteq SUBSET (1..2))
        /\ SUBSET {"a", "b"} \subseteq SUBSET {"a", "b", "c"}
        /\ ~(SUBSET {"a", "c"} \subseteq SUBSET {"a", "b"})
        /\ SUBSET Nat \subseteq SUBSET Int
        /\ ~(SUBSET Int \subseteq SUBSET Nat)
    )

Spec == Init /\ [][Next]_b

=============================================================================