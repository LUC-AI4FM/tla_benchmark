MODULE Barrier
EXTENDS Naturals, TLC

CONSTANTS N
ASSUME N > 0

VARIABLE pc

(* Process set *)
Proc == 1 .. N

(* Type correctness for the program counter *)
TypeOK ==
  /\ pc \in [Proc -> {"b0","b1"}]
  /\ \A p \in Proc : pc[p] = "b0" \/ pc[p] = "b1"

Init ==
  /\ TypeOK
  /\ pc = [p \in Proc |-> "b0"]

(* A single process moves from b0 to b1 *)
SingleEnter(p) ==
  /\ p \in Proc
  /\ pc[p] = "b0"
  /\ pc' = [pc EXCEPT ![p] = "b1"]

(* All processes reset from b1 to b0 simultaneously *)
ResetAll ==
  /\ (\A p \in Proc : pc[p] = "b1")
  /\ pc' = [p \in Proc |-> "b0"]

Next == (\E p \in Proc : SingleEnter(p)) \/ ResetAll

(* Barrier safety invariant: a process cannot leave the barrier until all have entered it *)
BarrierInvariant ==
  [] ( \A p \in Proc :
        (pc[p] = "b1" /\ ~(\A q \in Proc : pc[q] = "b1")) => pc'[p] = pc[p])

Spec == Init
       /\ [][Next]_<<pc>>
       /\ []TypeOK
       /\ BarrierInvariant

===============================================================================