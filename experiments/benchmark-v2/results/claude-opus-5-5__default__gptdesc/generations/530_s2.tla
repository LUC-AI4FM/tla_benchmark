------------------------------ MODULE TupleMax ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Tuples, minValue

ASSUME minValue \in Int
ASSUME Tuples \subseteq Seq(Int)
ASSUME \A t \in Tuples : \A n \in 1..Len(t) : t[n] >= minValue

(***************************************************************************
--algorithm TupleMax
variables inp \in Tuples, max = minValue, i = 1;
begin
  assert \A n \in 1..Len(inp) : inp[n] > minValue;
  lp: while i =< Len(inp) do
        if inp[i] > max then max := inp[i] end if;
        i := i + 1
      end while;
end algorithm
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES inp, max, i, pc

vars == << inp, max, i, pc >>

Init == (* Global variables *)
        /\ inp \in Tuples
        /\ max = minValue
        /\ i = 1
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(\A n \in 1..Len(inp) : inp[n] > minValue,
                   "Failure of assertion at line 4, column 3.")
         /\ pc' = "lp"
         /\ UNCHANGED << inp, max, i >>

lp == /\ pc = "lp"
      /\ IF i =< Len(inp)
            THEN /\ IF inp[i] > max
                       THEN /\ max' = inp[i]
                       ELSE /\ TRUE
                            /\ max' = max
                 /\ i' = i + 1
                 /\ pc' = "lp"
            ELSE /\ pc' = "Done"
                 /\ UNCHANGED << max, i >>
      /\ inp' = inp

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ lp
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")
\* END TRANSLATION

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK == /\ inp \in Tuples
          /\ max \in Int
          /\ i \in Nat
          /\ pc \in {"Lbl_1", "lp", "Done"}

\* On termination, max is the maximum element of inp (or minValue if inp is empty)
Correctness ==
    pc = "Done" =>
        /\ \A n \in 1..Len(inp) : inp[n] =< max
        /\ (Len(inp) > 0) => (\E n \in 1..Len(inp) : inp[n] = max)
        /\ (Len(inp) = 0) => (max = minValue)

\* Loop invariant: max is the maximum of the elements scanned so far
LoopInv ==
    pc = "lp" =>
        /\ i \in 1..(Len(inp) + 1)
        /\ \A n \in 1..(i - 1) : inp[n] =< max
        /\ (i > 1) => (\E n \in 1..(i - 1) : inp[n] = max)
        /\ (i = 1) => (max = minValue)

=============================================================================