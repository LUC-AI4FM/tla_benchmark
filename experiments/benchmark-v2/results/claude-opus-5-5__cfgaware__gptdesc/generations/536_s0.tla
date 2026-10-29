---- MODULE TupleMax ----
EXTENDS Integers, Sequences, TLC

CONSTANTS Tuples, minValue

ASSUME \A t \in Tuples : \A n \in 1..Len(t) : t[n] > minValue

(* --algorithm TupleMax
variables inp \in Tuples, max = minValue, I = 1..Len(inp);
begin
  Lbl_1:
    while I # {} do
      with i \in I do
        if inp[i] > max then
          max := inp[i]
        end if;
        I := I \ {i}
      end with
    end while
end algorithm *)

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
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << max, I >>
         /\ inp' = inp

Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

Correctness ==
  pc = "Done" =>
    IF inp = << >>
      THEN max = minValue
      ELSE /\ \E n \in 1..Len(inp) : max = inp[n]
           /\ \A n \in 1..Len(inp) : max >= inp[n]

TypeOK == /\ inp \in Tuples
          /\ max \in Int
          /\ I \subseteq 1..Len(inp)
          /\ pc \in {"Lbl_1", "Done"}

====