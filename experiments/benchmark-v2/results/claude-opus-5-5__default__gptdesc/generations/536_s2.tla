------------------------------- MODULE FindMax -------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Tuples, minValue

ASSUME \A t \in Tuples : \A n \in 1..Len(t) : t[n] > minValue

(***************************************************************************
--fair algorithm FindMax {
  variables inp \in Tuples, max = minValue, I = 1..Len(inp) ;
  { while (I # {}) {
      with (i \in I) {
        if (inp[i] > max) { max := inp[i] } ;
        I := I \ {i}
      }
    }
  }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
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

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

TypeOK == /\ inp \in Tuples
          /\ max \in Int
          /\ I \subseteq 1..Len(inp)
          /\ pc \in {"Lbl_1", "Done"}

Correctness ==
  pc = "Done" =>
     IF inp = << >>
       THEN max = minValue
       ELSE /\ \E n \in 1..Len(inp) : max = inp[n]
            /\ \A n \in 1..Len(inp) : inp[n] =< max

THEOREM Spec => []Correctness
THEOREM Spec => Termination
=============================================================================