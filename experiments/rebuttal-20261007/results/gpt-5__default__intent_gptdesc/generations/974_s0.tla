------------------------------ MODULE RegularRing ------------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 1

(*
  Processes are 1..N arranged in a ring; each process p writes to reg[p].
  Values are from {0,1}; A is the value written by each process.
*)
Val  == {0, 1}
A    == 1
Proc == 1..N

Left(p) == IF p = 1 THEN N ELSE p - 1

VARIABLES pc, reg, loc

vars == << pc, reg, loc >>

Init ==
  /\ pc  = [p \in Proc |-> "bw"]
  /\ reg = [p \in Proc |-> {0}]
  /\ loc = [p \in Proc |-> 0]

(*
  BeginWrite(p): start writing A to reg[p].
  Regular-register semantics during a write: reads may return old or new,
  so reg[p] becomes the union of its current possible values with {A}.
*)
BeginWrite(p) ==
  /\ p \in Proc
  /\ pc[p] = "bw"
  /\ pc'  = [pc EXCEPT ![p] = "cw"]
  /\ reg' = [reg EXCEPT ![p] = reg[p] \cup {A}]
  /\ loc' = loc

(*
  CompleteWrite(p): finish the write so the register thereafter contains A.
  After completion, reads must return A, so reg[p] becomes {A}.
*)
CompleteWrite(p) ==
  /\ p \in Proc
  /\ pc[p] = "cw"
  /\ pc'  = [pc EXCEPT ![p] = "rd"]
  /\ reg' = [reg EXCEPT ![p] = {A}]
  /\ loc' = loc

(*
  ReadStep(p): read the left neighbor's register and store the observed value.
  Regular-register read returns any value in the neighbor's current possible set.
*)
ReadStep(p) ==
  /\ p \in Proc
  /\ pc[p] = "rd"
  /\ \E v \in reg[Left(p)]:
       /\ pc'  = [pc EXCEPT ![p] = "done"]
       /\ loc' = [loc EXCEPT ![p] = v]
       /\ reg' = reg

Next ==
  \E p \in Proc:
       BeginWrite(p)
    \/ CompleteWrite(p)
    \/ ReadStep(p)

Spec == Init /\ [][Next]_vars

(*
  Type invariants:
  - pc is in the set of control states {"bw","cw","rd","done"}.
  - loc holds a value in {0,1}.
  - reg[p] is always a nonempty subset of {0,1}, representing possible read results.
*)
TypeOK ==
  /\ pc \in [Proc -> {"bw","cw","rd","done"}]
  /\ loc \in [Proc -> Val]
  /\ reg \in [Proc -> SUBSET Val]
  /\ \A p \in Proc: reg[p] # {}

(*
  Safety property: If all processes terminate, then at least one process read 1.
*)
AllTerminated == \A p \in Proc: pc[p] = "done"
SomeRead1     == \E p \in Proc: loc[p] = 1

Safety == [](AllTerminated => SomeRead1)

(*
  Progress/termination (possibility) property: it is possible that all processes eventually terminate.
*)
TerminationPossible == <> AllTerminated

===============================================================================