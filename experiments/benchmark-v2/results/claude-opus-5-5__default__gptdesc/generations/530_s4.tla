---------------------------- MODULE TupleMax ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Tuples, minValue

ASSUME minValue \in Int
ASSUME Tuples \subseteq Seq(Int)
ASSUME \A t \in Tuples : \A n \in 1..Len(t) : t[n] >= minValue

(***************************************************************************
--algorithm TupleMax {
  variables inp \in Tuples, max = minValue, i = 1;
  {
    Lbl_1: assert \A n \in 1..Len(inp) : inp[n] > minValue;
    Lbl_2: while (i =< Len(inp)) {
             if (inp[i] > max) { max := inp[i] };
             i := i + 1
           }
  }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES inp, max, i, pc

vars == << inp, max, i, pc >>

Init == /\ inp \in Tuples
        /\ max = minValue
        /\ i = 1
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(\A n \in 1..Len(inp) : inp[n] > minValue,
                   "Failure of assertion at line 8, column 12.")
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << inp, max, i >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF i <= Len(inp)
               THEN /\ IF inp[i] > max
                          THEN max' = inp[i]
                          ELSE max' = max
                    /\ i' = i + 1
                    /\ pc' = "Lbl_2"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << max, i >>
         /\ inp' = inp

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2 \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")
\* END TRANSLATION

TypeOK == /\ inp \in Tuples
          /\ max \in Int
          /\ i \in 1..(Len(inp) + 1)
          /\ pc \in {"Lbl_1", "Lbl_2", "Done"}

MaxCorrect ==
  (pc = "Done") =>
     /\ \A n \in 1..Len(inp) : max >= inp[n]
     /\ (Len(inp) > 0) => \E n \in 1..Len(inp) : max = inp[n]
     /\ (Len(inp) = 0) => max = minValue
=============================================================================