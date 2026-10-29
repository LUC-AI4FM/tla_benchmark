---------------------------- MODULE TupleMax ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Tuples, minValue

ASSUME Tuples \subseteq Seq(Int)
ASSUME minValue \in Int
ASSUME \A t \in Tuples : \A j \in 1..Len(t) : t[j] >= minValue

(* --algorithm TupleMax
variables inp \in Tuples, max = minValue, i = 1;
begin
  Lbl_1:
    assert \A n \in 1..Len(inp) : inp[n] > minValue;
  lp:
    while i <= Len(inp) do
      if inp[i] > max then
        max := inp[i]
      end if;
      i := i + 1
    end while
end algorithm *)

\* BEGIN TRANSLATION
VARIABLES inp, max, i, pc

vars == << inp, max, i, pc >>

Init == /\ inp \in Tuples
        /\ max = minValue
        /\ i = 1
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(\A n \in 1..Len(inp) : inp[n] > minValue,
                   "Failure of assertion at line 15, column 5.")
         /\ pc' = "lp"
         /\ UNCHANGED << inp, max, i >>

lp == /\ pc = "lp"
      /\ IF i <= Len(inp)
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

Next == Lbl_1 \/ lp \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")
\* END TRANSLATION

=============================================================================