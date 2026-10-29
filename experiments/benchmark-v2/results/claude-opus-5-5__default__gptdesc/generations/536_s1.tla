-------------------------------- MODULE Max --------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS minValue, Tuples

ASSUME /\ minValue \in Int
       /\ Tuples \subseteq Seq(Int)
       /\ \A t \in Tuples : \A j \in 1..Len(t) : t[j] > minValue

(***************************************************************************
--algorithm Max {
  variables max = minValue, inp \in Tuples, I = 1..Len(inp) ;
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
VARIABLES max, inp, I, pc

vars == << max, inp, I, pc >>

Init == /\ max = minValue
        /\ inp \in Tuples
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

-----------------------------------------------------------------------------

TypeOK == /\ max \in Int
          /\ inp \in Tuples
          /\ I \subseteq 1..Len(inp)
          /\ pc \in {"Lbl_1", "Done"}

Correctness ==
  pc = "Done" =>
     IF inp = << >>
       THEN max = minValue
       ELSE /\ \E j \in 1..Len(inp) : max = inp[j]
            /\ \A j \in 1..Len(inp) : max >= inp[j]

THEOREM Spec => [](TypeOK /\ Correctness)
THEOREM Spec => Termination
=============================================================================