---------------------------- MODULE Squares ----------------------------
EXTENDS Naturals, Integers, TLC

CONSTANT n

ASSUME n \in Nat

(* --algorithm Squares
variables x = [j \in 0..n |-> 0], i = 0;
begin
  a: while i < n do
       i := i + 1;
       x[i] := x[i-1] + (2*i - 1);
     end while;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES x, i, pc

vars == << x, i, pc >>

Init == /\ x = [j \in 0..n |-> 0]
        /\ i = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF i < n
           THEN /\ i' = i + 1
                /\ x' = [x EXCEPT ![i + 1] = x[(i + 1) - 1] + (2 * (i + 1) - 1)]
                /\ pc' = "a"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << x, i >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

(* Safety invariants *)
TypeOK == /\ x \in [0..n -> Nat]
          /\ i \in 0..n
          /\ pc \in {"a", "Done"}

SquaresCorrect == \A k \in 0..i : x[k] = k * k

DoneCorrect == (pc = "Done") => (i = n /\ \A k \in 0..n : x[k] = k * k)

=============================================================================