------------------------------ MODULE RegularRegisters ------------------------------
EXTENDS Naturals, TLC

CONSTANT N
CONSTANTS Start, Writing, Completed, Terminated

VARIABLES regs, pending, localVal, PC

(* Set of processes *)
Proc == 1..N

States == {Start, Writing, Completed, Terminated}

(* Initial state *)
Init ==
  /\ regs = [i ∈ Proc |-> 0]
  /\ pending = [i ∈ Proc |-> ⊥]
  /\ localVal = [i ∈ Proc |-> 0]
  /\ PC = [i ∈ Proc |-> Start]

(* Actions for a single process i *)
BeginWrite(i) ==
  /\ i ∈ Proc
  /\ PC[i] = Start
  /\ pending' = [pending EXCEPT ![i] = 1]
  /\ PC' = [PC EXCEPT ![i] = Writing]
  /\ UNCHANGED <<regs, localVal>>

CompleteWrite(i) ==
  /\ i ∈ Proc
  /\ PC[i] = Writing
  /\ regs' = [regs EXCEPT ![i] = pending[i]]
  /\ pending' = [pending EXCEPT ![i] = ⊥]
  /\ PC' = [PC EXCEPT ![i] = Completed]
  /\ UNCHANGED localVal

ReadNeighbor(i) ==
  /\ i ∈ Proc
  /\ PC[i] = Completed
  /\ j == IF i > 1 THEN i-1 ELSE N
  /\ v ∈ {regs[j]} \cup (IF pending[j] ≠ ⊥ THEN {pending[j]} ELSE {})
  /\ localVal' = [localVal EXCEPT ![i] = v]
  /\ PC' = [PC EXCEPT ![i] = Terminated]
  /\ UNCHANGED <<regs, pending>>

(* Next-state relation *)
Next ==
  ∨ i ∈ Proc :
      BeginWrite(i) \/ CompleteWrite(i) \/ ReadNeighbor(i)

vars == {regs, pending, localVal, PC}

Spec == Init /\ [][Next]_vars

(* Type invariant *)
TypeOK ==
  /\ ∀ i ∈ Proc : regs[i] ∈ {0,1}
  /\ ∀ i ∈ Proc : pending[i] = ⊥ \/ pending[i] ∈ {0,1}
  /\ ∀ i ∈ Proc : localVal[i] ∈ {0,1}
  /\ ∀ i ∈ Proc : PC[i] ∈ States

(* Program counter correctness *)
PCorrect ==
  ∀ i ∈ Proc : PC[i] ∈ States

(* Safety invariant: if all processes terminated then at least one read 1 *)
Inv ==
  (∀ i ∈ Proc : PC[i] = Terminated) ⇒ (∃ i ∈ Proc : localVal[i] = 1)

(* Progress property: it is possible that all processes eventually terminate *)
PossibleTermination == ◇ (∀ i ∈ Proc : PC[i] = Terminated)

=============================================================================