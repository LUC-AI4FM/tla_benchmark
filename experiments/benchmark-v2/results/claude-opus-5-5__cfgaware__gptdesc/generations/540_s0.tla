---------------------------- MODULE Squares ----------------------------
EXTENDS Naturals, Integers, TLC

CONSTANT NSet

ASSUME NSet \subseteq Nat

(* --algorithm Squares
variables n \in NSet,
          x = [j \in 0..n |-> 0],
          i = 0,
          a = 0;
begin
Lbl_1:
  while i < n do
Lbl_2:
    i := i + 1;
    x[i] := x[i-1] + (2*i - 1);
  end while;
Lbl_3:
  a := x[n];
end algorithm *)

\* BEGIN TRANSLATION
VARIABLES n, x, i, a, pc

vars == << n, x, i, a, pc >>

Init == /\ n \in NSet
        /\ x = [j \in 0..n |-> 0]
        /\ i = 0
        /\ a = 0
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF i < n
               THEN /\ pc' = "Lbl_2"
               ELSE /\ pc' = "Lbl_3"
         /\ UNCHANGED << n, x, i, a >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ i' = i + 1
         /\ x' = [x EXCEPT ![i + 1] = x[i] + (2*(i + 1) - 1)]
         /\ pc' = "Lbl_1"
         /\ UNCHANGED << n, a >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ a' = x[n]
         /\ pc' = "Done"
         /\ UNCHANGED << n, x, i >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

TypeOK == /\ n \in NSet
          /\ i \in 0..n
          /\ x \in [0..n -> Nat]
          /\ pc \in {"Lbl_1", "Lbl_2", "Lbl_3", "Done"}

Correct == pc = "Done" => (a = n * n /\ \A j \in 0..n : x[j] = j * j)

=============================================================================