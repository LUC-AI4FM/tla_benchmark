------------------------------ MODULE RegularRing ------------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 1

(*
  Processes are indexed 0 .. N-1 on a ring.
  Each process i owns shared register reg[i] and a private local register l[i].
*)

Proc == 0 .. (N - 1)

Left(i)  == IF i = 0 THEN N - 1 ELSE i - 1
Right(i) == IF i = N - 1 THEN 0 ELSE i + 1

RegState == {"S0", "X01", "S1"}   \* S0: stable 0, X01: transitional 0->1 (regular), S1: stable 1
PC       == {"start", "begun", "written", "done"}
LocalVal == {"U", 0, 1}
NoProc   == "NoProc"

VARIABLES
  pc,           \* control state of each process
  reg,          \* state of each shared register
  l,            \* local (private) register of each process
  firstWriter   \* ghost variable recording the first process to complete its write (if any)

vars == << pc, reg, l, firstWriter >>

Init ==
  /\ pc = [i \in Proc |-> "start"]
  /\ reg = [i \in Proc |-> "S0"]
  /\ l = [i \in Proc |-> "U"]
  /\ firstWriter = NoProc

ReadSet(j) ==
  IF reg[j] = "S0" THEN {0}
  ELSE IF reg[j] = "S1" THEN {1}
  ELSE {0, 1}

BeginWrite(i) ==
  /\ i \in Proc
  /\ pc[i] = "start"
  /\ reg[i] = "S0"
  /\ pc' = [pc EXCEPT ![i] = "begun"]
  /\ reg' = [reg EXCEPT ![i] = "X01"]
  /\ UNCHANGED << l, firstWriter >>

CompleteWrite(i) ==
  /\ i \in Proc
  /\ pc[i] = "begun"
  /\ reg[i] = "X01"
  /\ pc' = [pc EXCEPT ![i] = "written"]
  /\ reg' = [reg EXCEPT ![i] = "S1"]
  /\ firstWriter' = IF firstWriter = NoProc THEN i ELSE firstWriter
  /\ UNCHANGED l

ReadLeft(i) ==
  /\ i \in Proc
  /\ pc[i] = "written"
  /\ \E v \in ReadSet(Left(i)):
       /\ pc' = [pc EXCEPT ![i] = "done"]
       /\ l'  = [l  EXCEPT ![i] = v]
       /\ UNCHANGED << reg, firstWriter >>

ProcStep(i) == BeginWrite(i) \/ CompleteWrite(i) \/ ReadLeft(i)

Next == \E i \in Proc: ProcStep(i)

Fair == \A i \in Proc: WF_vars(ProcStep(i))

Spec == Init /\ [][Next]_vars /\ Fair

(*
  Safety invariants (state predicates)
*)

TypeInv ==
  /\ pc \in [Proc -> PC]
  /\ reg \in [Proc -> RegState]
  /\ l \in [Proc -> LocalVal]
  /\ firstWriter = NoProc \/ firstWriter \in Proc

PCRegInv ==
  /\ \A i \in Proc:
       /\ (pc[i] = "start"   => reg[i] = "S0")
       /\ (pc[i] = "begun"   => reg[i] = "X01")
       /\ (pc[i] \in {"written","done"} => reg[i] = "S1")
  /\ \A i \in Proc: (pc[i] = "done" => l[i] \in {0,1})

AllDone == \A i \in Proc: pc[i] = "done"

KeySafety ==
  AllDone => (\E i \in Proc: l[i] = 1)

(*
  Inductive invariant establishing KeySafety:
  Once the first writer completes (firstWriter \in Proc),
  its right neighbor must read 1 (since the first writer's register is stably 1 before any other completion),
  hence either that neighbor is not yet done or its local value is 1.
*)
SafetyInv ==
  (firstWriter = NoProc)
  \/ LET fw == firstWriter IN
       IF fw \in Proc
       THEN (pc[Right(fw)] # "done") \/ (l[Right(fw)] = 1)
       ELSE TRUE

InductiveInv == TypeInv /\ PCRegInv /\ SafetyInv

(*
  Liveness property: all processes eventually complete.
*)
Termination == <>AllDone

=============================================================================