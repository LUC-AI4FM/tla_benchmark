---------------------------- MODULE FindMax ----------------------------
EXTENDS Integers, Sequences, FiniteSets

(***************************************************************************)
(* The set of possible input sequences: all sequences of length 0..3 with *)
(* elements drawn from 0..3.                                               *)
(***************************************************************************)
Tuples == UNION { [1..n -> 0..3] : n \in 0..3 }

(***************************************************************************)
(* A lower bound strictly smaller than every possible element.            *)
(***************************************************************************)
minValue == -1

VARIABLES inp, max, I

vars == << inp, max, I >>

TypeOK ==
    /\ inp \in Tuples
    /\ max \in {minValue} \cup (0..3)
    /\ I \subseteq 1..Len(inp)

Init ==
    /\ inp \in Tuples
    /\ max = minValue
    /\ I = 1..Len(inp)

Step ==
    /\ I # {}
    /\ \E i \in I :
         /\ max' = IF inp[i] > max THEN inp[i] ELSE max
         /\ I' = I \ {i}
    /\ UNCHANGED inp

Done ==
    /\ I = {}
    /\ UNCHANGED vars

Next == Step \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------
(* Safety *)

Correctness ==
    I = {} =>
        IF Len(inp) = 0
          THEN max = minValue
          ELSE /\ \E j \in 1..Len(inp) : max = inp[j]
               /\ \A j \in 1..Len(inp) : max >= inp[j]

Inv == TypeOK /\ Correctness

(* Liveness *)

Termination == <>(I = {})

THEOREM Spec => [](TypeOK /\ Correctness)
THEOREM Spec => Termination
=============================================================================