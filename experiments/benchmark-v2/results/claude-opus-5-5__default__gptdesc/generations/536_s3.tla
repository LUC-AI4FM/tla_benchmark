---------------------------- MODULE MaxAlgorithm ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS minValue, Tuples

ASSUME \A t \in Tuples : \A k \in 1..Len(t) : t[k] > minValue

(***************************************************************************
--algorithm Max {
  variables inp \in Tuples, max = minValue, I = 1..Len(inp);
  {
    a: while (I # {}) {
         with (i \in I) {
           if (inp[i] > max) { max := inp[i] };
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
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF I # {}
           THEN /\ \E i \in I :
                     /\ max' = (IF inp[i] > max THEN inp[i] ELSE max)
                     /\ I' = I \ {i}
                /\ pc' = "a"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << max, I >>
     /\ UNCHANGED inp

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

TypeOK == /\ inp \in Tuples
          /\ max \in Int
          /\ I \subseteq 1..Len(inp)
          /\ pc \in {"a", "Done"}

Correctness ==
    pc = "Done" =>
        IF inp = << >>
           THEN max = minValue
           ELSE /\ \E n \in 1..Len(inp) : max = inp[n]
                /\ \A n \in 1..Len(inp) : inp[n] <= max

THEOREM Spec => []Correctness
THEOREM Spec => Termination
=============================================================================