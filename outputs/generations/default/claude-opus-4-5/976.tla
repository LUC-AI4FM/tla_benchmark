---------------------------- MODULE SimpleRingAlgorithm ----------------------------
EXTENDS Naturals, TLAPS

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES x, y, pc

vars == <<x, y, pc>>

Procs == 1..N

Init == 
    /\ x = [i \in Procs |-> 0]
    /\ y = [i \in Procs |-> 0]
    /\ pc = [i \in Procs |-> "s1"]

\* Left neighbor in the ring (wraps around)
Left(i) == IF i = 1 THEN N ELSE i - 1

\* Process i sets its own x entry to 1
s1(i) == 
    /\ pc[i] = "s1"
    /\ x' = [x EXCEPT ![i] = 1]
    /\ y' = y
    /\ pc' = [pc EXCEPT ![i] = "s2"]

\* Process i copies left neighbor's x value into its own y entry
s2(i) == 
    /\ pc[i] = "s2"
    /\ y' = [y EXCEPT ![i] = x[Left(i)]]
    /\ x' = x
    /\ pc' = [pc EXCEPT ![i] = "Done"]

\* Process i is done
Done(i) == 
    /\ pc[i] = "Done"
    /\ UNCHANGED vars

Next == \E i \in Procs : s1(i) \/ s2(i) \/ Done(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* All processes have terminated
AllDone == \A i \in Procs : pc[i] = "Done"

\* Termination: eventually all processes complete
Termination == <>AllDone

\* Type correctness invariant
TypeOK == 
    /\ x \in [Procs -> {0, 1}]
    /\ y \in [Procs -> {0, 1}]
    /\ pc \in [Procs -> {"s1", "s2", "Done"}]

\* Safety property: when all processes are done, at least one has y[i] = 1
Safety == AllDone => \E i \in Procs : y[i] = 1

\* Inductive invariant components

\* If a process has passed s1, its x is 1
Inv1 == \A i \in Procs : pc[i] \in {"s2", "Done"} => x[i] = 1

\* If a process is done, its y equals the left neighbor's x at some point
\* More precisely: if process i is done and left neighbor passed s1 before i read, then y[i] = 1
Inv2 == \A i \in Procs : 
    (pc[i] = "Done" /\ pc[Left(i)] \in {"s2", "Done"}) => 
    (y[i] = 1 \/ x[Left(i)] = 1)

\* Key insight: there exists some process that was "last" to execute s1
\* That process's right neighbor will see x=1 when copying
\* Stronger invariant: once any process sets x[i]=1, it stays 1
Inv3 == \A i \in Procs : x[i] = 1 => pc[i] \in {"s2", "Done"}

\* If all processes are done, at least one saw its left neighbor's x as 1
\* This follows because the last process to execute s2 must have seen x[Left(i)] = 1
\* since its left neighbor already executed s1

\* Complete inductive invariant
Inv == 
    /\ TypeOK
    /\ Inv1
    /\ \A i \in Procs : pc[i] = "Done" => 
        (pc[Left(i)] \in {"s2", "Done"} => y[i] = 1 \/ y[Left(i)] = 1)

\* Main correctness theorem: Safety holds
THEOREM SafetyTheorem == Spec => []Safety
<1>1. Init => TypeOK
  <2>1. ASSUME Init PROVE TypeOK
    BY <2>1 DEF Init, TypeOK, Procs
  <2>. QED BY <2>1
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2>1. ASSUME TypeOK, Next PROVE TypeOK'
    BY <2>1 DEF TypeOK, Next, s1, s2, Done, Procs, Left, vars
  <2>2. ASSUME TypeOK, UNCHANGED vars PROVE TypeOK'
    BY <2>2 DEF TypeOK, vars
  <2>. QED BY <2>1, <2>2
<1>3. Init => Inv1
  <2>1. ASSUME Init PROVE Inv1
    BY <2>1 DEF Init, Inv1, Procs
  <2>. QED BY <2>1
<1>4. Inv1 /\ [Next]_vars => Inv1'
  <2>1. ASSUME Inv1, Next PROVE Inv1'
    BY <2>1 DEF Inv1, Next, s1, s2, Done, Procs, vars
  <2>2. ASSUME Inv1, UNCHANGED vars PROVE Inv1'
    BY <2>2 DEF Inv1, vars
  <2>. QED BY <2>1, <2>2
<1>5. TypeOK /\ Inv1 /\ AllDone => Safety
  <2>1. ASSUME TypeOK, Inv1, AllDone PROVE Safety
    <3>1. \A i \in Procs : x[i] = 1
      BY <2>1 DEF Inv1, AllDone, Procs
    <3>2. \A i \in Procs : x[Left(i)] = 1
      BY <3>1, NAssumption DEF Left, Procs
    <3>. QED BY <2>1, <3>1, <3>2, NAssumption DEF Safety, AllDone, Procs
  <2>. QED BY <2>1
<1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Spec, Safety

\* Alternative proof version with explicit invariant
THEOREM SafetyTheoremV2 == Spec => []Safety
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK, Inv1, Procs
<1>2. Inv /\ [Next]_vars => Inv'
  <2>1. ASSUME Inv, Next PROVE Inv'
    BY <2>1 DEF Inv, TypeOK, Inv1, Next, s1, s2, Done, Procs, Left, vars
  <2>2. ASSUME Inv, UNCHANGED vars PROVE Inv'
    BY <2>2 DEF Inv, TypeOK, Inv1, vars
  <2>. QED BY <2>1, <2>2
<1>3. Inv => Safety
  <2>1. ASSUME Inv, AllDone PROVE \E i \in Procs : y[i] = 1
    <3>1. \A i \in Procs : x[i] = 1
      BY <2>1 DEF Inv, Inv1, AllDone, Procs
    <3>2. N \in Procs
      BY NAssumption DEF Procs
    <3>3. x[Left(N)] = 1
      BY <3>1, <3>2, NAssumption DEF Left, Procs
    <3>. QED BY <2>1, <3>1, NAssumption DEF Procs, AllDone, Inv, TypeOK
  <2>. QED BY <2>1 DEF Safety
<1>. QED BY <1>1, <1>2, <1>3 DEF Spec

===================================================================================