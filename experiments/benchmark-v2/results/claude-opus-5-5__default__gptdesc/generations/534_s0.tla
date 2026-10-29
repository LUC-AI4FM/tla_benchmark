------------------------------ MODULE TupleMax ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Tuples, minValue

ASSUME /\ minValue \in Int
       /\ Tuples \subseteq Seq(Int)
       /\ \A t \in Tuples : \A n \in 1..Len(t) : t[n] > minValue

(***************************************************************************
--algorithm TupleMax {
  variables inp \in Tuples, max = minValue, I = 1..Len(inp) ;
  { lb: while (I # {}) {
          with (i \in I) {
            if (inp[i] > max) { max := inp[i] } ;
            I := I \ {i}
          }
        } ;
        assert IF inp = << >> THEN max = minValue
               ELSE /\ \E n \in 1..Len(inp) : max = inp[n]
                    /\ \A n \in 1..Len(inp) : max >= inp[n]
  }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES inp, max, I, pc

vars == << inp, max, I, pc >>

Init == (* Global variables *)
        /\ inp \in Tuples
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
                           "Failure of assertion at line 9, column 9.")
                 /\ pc' = "Done"
                 /\ UNCHANGED << max, I >>
      /\ inp' = inp

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == lb
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

(***************************************************************************)
(* Additional safety properties                                            *)
(***************************************************************************)
TypeOK == /\ inp \in Tuples
          /\ max \in Int
          /\ I \subseteq 1..Len(inp)
          /\ pc \in {"lb", "Done"}

Correctness ==
    pc = "Done" =>
        IF inp = << >>
           THEN max = minValue
           ELSE /\ \E n \in 1..Len(inp) : max = inp[n]
                /\ \A n \in 1..Len(inp) : max >= inp[n]

=============================================================================