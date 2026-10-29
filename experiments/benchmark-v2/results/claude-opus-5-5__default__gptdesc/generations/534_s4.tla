---------------------------- MODULE TupleMax ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Tuples, minValue

ASSUME \A t \in Tuples : \A n \in 1..Len(t) : t[n] > minValue

(***************************************************************************
--algorithm TupleMax {
  variables inp \in Tuples, max = minValue, I = 1..Len(inp);
  { a: while (I # {}) {
         with (i \in I) {
           if (inp[i] > max) { max := inp[i] };
           I := I \ {i}
         }
       };
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
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF I # {}
           THEN /\ \E i \in I :
                     /\ IF inp[i] > max
                           THEN /\ max' = inp[i]
                           ELSE /\ TRUE
                                /\ max' = max
                     /\ I' = I \ {i}
                /\ pc' = "a"
           ELSE /\ Assert(IF inp = << >> THEN max = minValue
                          ELSE /\ \E n \in 1..Len(inp) : max = inp[n]
                               /\ \A n \in 1..Len(inp) : max >= inp[n],
                          "Failure of assertion at line 9, column 8.")
                /\ pc' = "Done"
                /\ UNCHANGED << max, I >>
     /\ inp' = inp

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

(***************************************************************************)
(* Safety: the correctness condition checked by the assertion, stated     *)
(* as an invariant that must hold upon termination.                        *)
(***************************************************************************)
Correctness ==
    pc = "Done" =>
        IF inp = << >> THEN max = minValue
        ELSE /\ \E n \in 1..Len(inp) : max = inp[n]
             /\ \A n \in 1..Len(inp) : max >= inp[n]

TypeOK ==
    /\ inp \in Tuples
    /\ max \in Int
    /\ I \subseteq 1..Len(inp)
    /\ pc \in {"a", "Done"}

=============================================================================