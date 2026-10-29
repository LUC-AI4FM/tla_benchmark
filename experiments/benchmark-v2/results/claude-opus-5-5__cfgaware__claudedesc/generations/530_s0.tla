---------------------------- MODULE TupleMax ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS minValue, Tuples

ASSUME minValue \in Int
ASSUME \A t \in Tuples : \A k \in 1..Len(t) : t[k] \in Int /\ t[k] >= minValue

(***************************************************************************
--algorithm TupleMax {
    variables inp \in Tuples, max = minValue, i = 1;
    {
    a1: assert \A n \in 1..Len(inp) : inp[n] > minValue;
    a2: while (i =< Len(inp)) {
          if (inp[i] > max) { max := inp[i] };
          i := i + 1
        };
    a3: assert IF inp = << >> THEN max = minValue
               ELSE /\ \E n \in 1..Len(inp) : max = inp[n]
                    /\ \A n \in 1..Len(inp) : max >= inp[n]
    }
}
***************************************************************************)

VARIABLES inp, max, i, pc

vars == << inp, max, i, pc >>

Init == /\ inp \in Tuples
        /\ max = minValue
        /\ i = 1
        /\ pc = "a1"

a1 == /\ pc = "a1"
      /\ Assert(\A n \in 1..Len(inp) : inp[n] > minValue,
                "Failure of assertion at line a1.")
      /\ pc' = "a2"
      /\ UNCHANGED << inp, max, i >>

a2 == /\ pc = "a2"
      /\ IF i =< Len(inp)
            THEN /\ IF inp[i] > max
                       THEN max' = inp[i]
                       ELSE max' = max
                 /\ i' = i + 1
                 /\ pc' = "a2"
            ELSE /\ pc' = "a3"
                 /\ UNCHANGED << max, i >>
      /\ inp' = inp

a3 == /\ pc = "a3"
      /\ Assert(IF inp = << >> THEN max = minValue
                ELSE /\ \E n \in 1..Len(inp) : max = inp[n]
                     /\ \A n \in 1..Len(inp) : max >= inp[n],
                "Failure of assertion at line a3.")
      /\ pc' = "Done"
      /\ UNCHANGED << inp, max, i >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a1 \/ a2 \/ a3 \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

=============================================================================