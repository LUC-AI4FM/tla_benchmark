---------------------------- MODULE TupleMax ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS minValue, Tuples

ASSUME minValue \in Int
ASSUME \A t \in Tuples : \A n \in 1..Len(t) : t[n] \in Int /\ t[n] >= minValue

VARIABLES inp, max, i, pc

vars == << inp, max, i, pc >>

Init ==
    /\ inp \in Tuples
    /\ max = minValue
    /\ i = 1
    /\ pc = "Lbl_1"

Lbl_1 ==
    /\ pc = "Lbl_1"
    /\ Assert(\A n \in 1..Len(inp) : inp[n] > minValue,
              "Failure of assertion at Lbl_1: input elements must exceed minValue.")
    /\ pc' = "Lbl_2"
    /\ UNCHANGED << inp, max, i >>

Lbl_2 ==
    /\ pc = "Lbl_2"
    /\ IF i <= Len(inp)
          THEN /\ IF max < inp[i]
                     THEN max' = inp[i]
                     ELSE max' = max
               /\ i' = i + 1
               /\ pc' = "Lbl_2"
          ELSE /\ pc' = "Lbl_3"
               /\ UNCHANGED << max, i >>
    /\ UNCHANGED inp

Lbl_3 ==
    /\ pc = "Lbl_3"
    /\ Assert(IF inp = << >>
                 THEN max = minValue
                 ELSE /\ \E n \in 1..Len(inp) : max = inp[n]
                      /\ \A n \in 1..Len(inp) : max >= inp[n],
              "Failure of assertion at Lbl_3: max is not the maximum of inp.")
    /\ pc' = "Done"
    /\ UNCHANGED << inp, max, i >>

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Terminating

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

Termination == <>(pc = "Done")

TypeOK ==
    /\ inp \in Tuples
    /\ max \in Int
    /\ i \in Nat
    /\ pc \in {"Lbl_1", "Lbl_2", "Lbl_3", "Done"}

=============================================================================