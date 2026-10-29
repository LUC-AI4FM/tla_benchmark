------------------------------- MODULE Max -------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Tuples, minValue

ASSUME /\ minValue \in Int
       /\ Tuples \subseteq Seq(Int)
       /\ \A t \in Tuples : \A k \in 1..Len(t) : t[k] > minValue

(***************************************************************************
--fair algorithm Max {
  variables max = minValue,
            inp \in Tuples,
            I = 1..Len(inp);
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
VARIABLES max, inp, I, pc

vars == << max, inp, I, pc >>

Init == /\ max = minValue
        /\ inp \in Tuples
        /\ I = 1..Len(inp)
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF I # {}
           THEN /\ \E i \in I :
                     /\ IF inp[i] > max
                           THEN max' = inp[i]
                           ELSE max' = max
                     /\ I' = I \ {i}
                /\ pc' = "a"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << max, I >>
     /\ inp' = inp

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

TypeOK == /\ max \in Int
          /\ inp \in Tuples
          /\ I \subseteq 1..Len(inp)
          /\ pc \in {"a", "Done"}

Correctness ==
  pc = "Done" =>
    IF inp = << >>
      THEN max = minValue
      ELSE /\ \E n \in 1..Len(inp) : max = inp[n]
           /\ \A n \in 1..Len(inp) : inp[n] <= max

THEOREM Spec => []TypeOK
THEOREM Spec => []Correctness
THEOREM Spec => Termination
=============================================================================