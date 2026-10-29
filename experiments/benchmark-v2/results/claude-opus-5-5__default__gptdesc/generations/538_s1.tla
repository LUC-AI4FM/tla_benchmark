---- MODULE SquareByOddSums ----
EXTENDS Naturals, TLC

CONSTANT NSet

ASSUME NSet \subseteq Nat

(* --algorithm Square
variables n \in NSet, x = 0, i = 0;
begin
  Loop:
    while i < n do
      i := i + 1;
      x := x + 2*i - 1;
    end while;
end algorithm; *)

VARIABLES n, x, i, pc

vars == << n, x, i, pc >>

Init == /\ n \in NSet
        /\ x = 0
        /\ i = 0
        /\ pc = "Loop"

Loop == /\ pc = "Loop"
        /\ IF i < n
              THEN /\ i' = i + 1
                   /\ x' = x + 2*(i + 1) - 1
                   /\ pc' = "Loop"
              ELSE /\ pc' = "Done"
                   /\ UNCHANGED << x, i >>
        /\ n' = n

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Loop
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

TypeOK == /\ n \in NSet
          /\ x \in Nat
          /\ i \in Nat
          /\ pc \in {"Loop", "Done"}

LoopInv == x = i * i

Correctness == (pc = "Done") => (x = n * n)

====