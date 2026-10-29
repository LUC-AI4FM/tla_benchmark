------------------------------ MODULE TupleMax ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Tuples, minValue

ASSUME \A t \in Tuples : \A k \in 1..Len(t) : minValue < t[k]

(***************************************************************************
--algorithm TupleMax
variables inp \in Tuples, max = minValue, I = 1..Len(inp);
begin
Lbl_1: while I # {} do
         with i \in I do
           if inp[i] > max then max := inp[i] end if;
           I := I \ {i}
         end with
       end while;
Lbl_2: assert IF inp = << >>
                THEN max = minValue
                ELSE /\ \E n \in 1..Len(inp) : max = inp[n]
                     /\ \A n \in 1..Len(inp) : max >= inp[n]
end algorithm
***************************************************************************)

VARIABLES inp, max, I, pc

vars == << inp, max, I, pc >>

Init == /\ inp \in Tuples
        /\ max = minValue
        /\ I = 1..Len(inp)
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF I # {}
               THEN /\ \E i \in I :
                         /\ IF inp[i] > max
                               THEN max' = inp[i]
                               ELSE max' = max
                         /\ I' = I \ {i}
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Lbl_2"
                    /\ UNCHANGED << max, I >>
         /\ inp' = inp

Lbl_2 == /\ pc = "Lbl_2"
         /\ Assert(IF inp = << >>
                      THEN max = minValue
                      ELSE /\ \E n \in 1..Len(inp) : max = inp[n]
                           /\ \A n \in 1..Len(inp) : max >= inp[n],
                   "Failure of assertion at Lbl_2.")
         /\ pc' = "Done"
         /\ UNCHANGED << inp, max, I >>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2 \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

=============================================================================