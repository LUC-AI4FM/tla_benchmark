---------------------------- MODULE SimpleRing ----------------------------
EXTENDS Integers, TLAPS, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES x, y, pc

vars == <<x, y, pc>>

Procs == 1..N

Init == 
    /\ x = [i \in Procs |-> 0]
    /\ y = [i \in Procs |-> 0]
    /\ pc = [i \in Procs |-> "SetX"]

(* PlusCal algorithm (in comments):
--algorithm SimpleRing
variables x = [i \in 1..N |-> 0], y = [i \in 1..N |-> 0];
process Proc \in 1..N
begin
  SetX: x[self] := 1;
  SetY: y[self] := x[((self - 2) % N) + 1];
  Done: skip;
end process
end algorithm
*)

LeftNeighbor(i) == ((i - 2) % N) + 1

SetX(self) ==
    /\ pc[self] = "SetX"
    /\ x' = [x EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "SetY"]
    /\ y' = y

SetY(self) ==
    /\ pc[self] = "SetY"
    /\ y' = [y EXCEPT ![self] = x[LeftNeighbor(self)]]
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ x' = x

DoneStep(self) ==
    /\ pc[self] = "Done"
    /\ UNCHANGED vars

Proc(self) == SetX(self) \/ SetY(self) \/ DoneStep(self)

Next == \E self \in Procs : Proc(self)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* Type correctness *)
TypeOK ==
    /\ x \in [Procs -> {0, 1}]
    /\ y \in [Procs -> {0, 1}]
    /\ pc \in [Procs -> {"SetX", "SetY", "Done"}]

(* All processes have finished *)
AllDone == \A i \in Procs : pc[i] = "Done"

(* Termination: eventually all processes complete *)
Termination == <>AllDone

(* Safety property: when all done, at least one process has y[i] = 1 *)
Safety == AllDone => \E i \in Procs : y[i] = 1

(* Inductive invariant *)
Inv ==
    /\ TypeOK
    /\ \A i \in Procs : pc[i] \in {"SetY", "Done"} => x[i] = 1
    /\ \A i \in Procs : pc[i] = "Done" => y[i] = x[LeftNeighbor(i)]
    /\ (\A i \in Procs : pc[i] # "SetX") => (\A i \in Procs : x[i] = 1)

(* THEOREM: Inv is an inductive invariant *)
THEOREM InitImpliesInv == Init => Inv
<1>1. Init => TypeOK
  BY NAssumption DEF Init, TypeOK, Procs
<1>2. Init => \A i \in Procs : pc[i] \in {"SetY", "Done"} => x[i] = 1
  BY DEF Init, Procs
<1>3. Init => \A i \in Procs : pc[i] = "Done" => y[i] = x[LeftNeighbor(i)]
  BY DEF Init, Procs
<1>4. Init => ((\A i \in Procs : pc[i] # "SetX") => (\A i \in Procs : x[i] = 1))
  BY DEF Init, Procs
<1>. QED BY <1>1, <1>2, <1>3, <1>4 DEF Inv

THEOREM InvPreservedByNext == Inv /\ Next => Inv'
<1>. SUFFICES ASSUME Inv, Next PROVE Inv' OBVIOUS
<1>1. PICK self \in Procs : Proc(self) BY DEF Next
<1>2. CASE SetX(self)
  <2>1. TypeOK' BY <1>2 DEF SetX, Inv, TypeOK, Procs
  <2>2. \A i \in Procs : pc'[i] \in {"SetY", "Done"} => x'[i] = 1
    BY <1>2 DEF SetX, Inv, Procs
  <2>3. \A i \in Procs : pc'[i] = "Done" => y'[i] = x'[LeftNeighbor(i)]
    BY <1>2 DEF SetX, Inv, Procs, LeftNeighbor
  <2>4. (\A i \in Procs : pc'[i] # "SetX") => (\A i \in Procs : x'[i] = 1)
    BY <1>2 DEF SetX, Inv, Procs
  <2>. QED BY <2>1, <2>2, <2>3, <2>4 DEF Inv
<1>3. CASE SetY(self)
  <2>1. TypeOK' BY <1>3 DEF SetY, Inv, TypeOK, Procs
  <2>2. \A i \in Procs : pc'[i] \in {"SetY", "Done"} => x'[i] = 1
    BY <1>3 DEF SetY, Inv, Procs
  <2>3. \A i \in Procs : pc'[i] = "Done" => y'[i] = x'[LeftNeighbor(i)]
    BY <1>3 DEF SetY, Inv, Procs, LeftNeighbor
  <2>4. (\A i \in Procs : pc'[i] # "SetX") => (\A i \in Procs : x'[i] = 1)
    BY <1>3 DEF SetY, Inv, Procs
  <2>. QED BY <2>1, <2>2, <2>3, <2>4 DEF Inv
<1>4. CASE DoneStep(self)
  BY <1>4 DEF DoneStep, Inv, TypeOK, vars
<1>. QED BY <1>1, <1>2, <1>3, <1>4 DEF Proc

(* THEOREM: Invariant implies safety (version 1 - direct proof) *)
THEOREM InvImpliesSafety_V1 == Inv => Safety
<1>. SUFFICES ASSUME Inv, AllDone PROVE \E i \in Procs : y[i] = 1 OBVIOUS DEF Safety
<1>1. \A i \in Procs : pc[i] = "Done" BY DEF AllDone
<1>2. \A i \in Procs : pc[i] # "SetX" BY <1>1
<1>3. \A i \in Procs : x[i] = 1 BY <1>2 DEF Inv
<1>4. PICK j \in Procs : TRUE BY NAssumption DEF Procs
<1>5. y[j] = x[LeftNeighbor(j)] BY <1>1 DEF Inv
<1>6. LeftNeighbor(j) \in Procs BY NAssumption DEF LeftNeighbor, Procs
<1>7. x[LeftNeighbor(j)] = 1 BY <1>3, <1>6
<1>8. y[j] = 1 BY <1>5, <1>7
<1>. QED BY <1>4, <1>8

(* THEOREM: Invariant implies safety (version 2 - using TypeOK explicitly) *)
THEOREM InvImpliesSafety_V2 == Inv => Safety
<1>. SUFFICES ASSUME Inv, AllDone PROVE \E i \in Procs : y[i] = 1 OBVIOUS DEF Safety
<1>1. TypeOK BY DEF Inv
<1>2. \A i \in Procs : pc[i] = "Done" BY DEF AllDone
<1>3. \A i \in Procs : pc[i] # "SetX" BY <1>2
<1>4. \A i \in Procs : x[i] = 1 BY <1>3 DEF Inv
<1>5. N >= 1 BY NAssumption
<1>6. 1 \in Procs BY <1>5 DEF Procs
<1>7. pc[1] = "Done" BY <1>2, <1>6
<1>8. y[1] = x[LeftNeighbor(1)] BY <1>7 DEF Inv
<1>9. LeftNeighbor(1) \in Procs BY NAssumption DEF LeftNeighbor, Procs
<1>10. x[LeftNeighbor(1)] = 1 BY <1>4, <1>9
<1>11. y[1] = 1 BY <1>8, <1>10
<1>. QED BY <1>6, <1>11

(* Main correctness theorem *)
THEOREM Correctness == Spec => []Safety
<1>1. Init => Inv BY InitImpliesInv
<1>2. Inv /\ [Next]_vars => Inv'
  <2>1. Inv /\ Next => Inv' BY InvPreservedByNext
  <2>2. Inv /\ UNCHANGED vars => Inv' BY DEF Inv, TypeOK, vars
  <2>. QED BY <2>1, <2>2
<1>3. Inv => Safety BY InvImpliesSafety_V1
<1>. QED BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================