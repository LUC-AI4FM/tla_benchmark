---------------------------- MODULE Squares ----------------------------
EXTENDS Naturals, TLC

NSet == 0..6

(* --algorithm Squares
variables n \in NSet,
          a = [j \in 1..n |-> 0],
          x = 0,
          i = 1;
begin
Loop:
  while i <= n do
Body:
    x := x + 2*i - 1;
    a[i] := x;
    i := i + 1;
  end while;
end algorithm *)

VARIABLES n, a, x, i, pc

vars == << n, a, x, i, pc >>

Init == /\ n \in NSet
        /\ a = [j \in 1..n |-> 0]
        /\ x = 0
        /\ i = 1
        /\ pc = "Loop"

Loop == /\ pc = "Loop"
        /\ IF i <= n
              THEN pc' = "Body"
              ELSE pc' = "Done"
        /\ UNCHANGED << n, a, x, i >>

Body == /\ pc = "Body"
        /\ x' = x + 2*i - 1
        /\ a' = [a EXCEPT ![i] = x']
        /\ i' = i + 1
        /\ pc' = "Loop"
        /\ n' = n

Terminating == /\ pc = "Done"
               /\ UNCHANGED vars

Next == Loop \/ Body \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Loop \/ Body)

TypeOK == /\ n \in NSet
          /\ a \in [1..n -> Nat]
          /\ x \in Nat
          /\ i \in 1..(n+1)
          /\ pc \in {"Loop", "Body", "Done"}

Invariant == /\ x = (i-1) * (i-1)
             /\ \A k \in 1..(i-1) : a[k] = k * k

Correctness == pc = "Done" => \A k \in 1..n : a[k] = k * k

Termination == <>(pc = "Done")

=============================================================================