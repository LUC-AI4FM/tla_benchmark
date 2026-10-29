---------------------------- MODULE FindMax ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Tuples, minValue

ASSUME \A t \in Tuples : \A k \in 1..Len(t) : t[k] > minValue

(***************************************************************************
--algorithm FindMax {
  variables inp \in Tuples, max = minValue, I = 1..Len(inp) ;
  {
    lb: while (I # {}) {
          with (i \in I) {
            if (inp[i] > max) { max := inp[i] } ;
            I := I \ {i}
          }
        } ;
        assert IF inp = << >>
                 THEN max = minValue
                 ELSE /\ \E n \in 1..Len(inp) : max = inp[n]
                      /\ \A n \in 1..Len(inp) : max >= inp[n]
  }
}
***************************************************************************)

VARIABLES inp, max, I, pc

vars == << inp, max, I, pc >>

Init == /\ inp \in Tuples
        /\ max = minValue
        /\ I = 1..Len(inp)
        /\ pc = "lb"

lb == /\ pc = "lb"
      /\ IF I # {}
            THEN /\ \E i \in I :
                      /\ IF inp[i] > max
                            THEN max' = inp[i]
                            ELSE max' = max
                      /\ I' = I \ {i}
                 /\ pc' = "lb"
            ELSE /\ Assert(IF inp = << >>
                             THEN max = minValue
                             ELSE /\ \E n \in 1..Len(inp) : max = inp[n]
                                  /\ \A n \in 1..Len(inp) : max >= inp[n],
                           "Failure of assertion at line 15, column 9.")
                 /\ pc' = "Done"
                 /\ UNCHANGED << max, I >>
      /\ inp' = inp

Terminating == pc = "Done" /\ UNCHANGED vars

Next == lb \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

=============================================================================