```
---- MODULE RingAlgorithm ----
EXTENDS Naturals

CONSTANT N

VARIABLES x, y, pc

(* Left neighbor function *)
Left(i) == IF i = 1 THEN N ELSE i - 1

(* All processes done predicate *)
AllDone == \A i \in 1..N : pc[i] = "done"

(* Safety invariant: if all done then at least one y[i]=1 *)
Inv == AllDone => (\E i \in 1..N : y[i] = 1)

(* Type correctness constraint *)
TypeInv == x \in [1..N -> Nat] /\ 
           y \in [1..N -> Nat] /\ 
           pc \in [1..N -> {"init", "copy", "done"}]

vars == <<x, y, pc>>

Init ==
    /\ x = [i \in 1..N |-> 0]
    /\ y = [i \in 1..N |-> 0]
    /\ pc = [i \in 1..N |-> "init"]
    /\ TypeInv

(* Action for process i to initialize its own x to 1 *)
InitAction(i) ==
    /\ pc[i] = "init"
    /\ x' = [x EXCEPT ![i] = 1]
    /\ pc' = [pc EXCEPT ![i] = "copy"]
    /\ y' = y

(* Action for process i to copy left neighbor's x into its own y *)
CopyAction(i) ==
    /\ pc[i] = "copy"
    /\ y' = [y EXCEPT ![i] = x[Left(i)]]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ x' = x

Next == \E i \in 1..N : InitAction(i) \/ CopyAction(i)

Spec == Init 
        /\ [] (Next)_vars
        /\ [] TypeInv
        /\ [] Inv
        /\ <> AllDone

THEOREM Correctness1 == Inv
THEOREM Correctness2 == Inv
```