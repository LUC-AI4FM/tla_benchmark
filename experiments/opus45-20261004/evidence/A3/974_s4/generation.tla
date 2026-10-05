---------------------------- MODULE RegularRegisters ----------------------------
EXTENDS Naturals, TLAPS, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES x, y, pc

vars == <<x, y, pc>>

Procs == 1..N

Neighbor(i) == IF i = N THEN 1 ELSE i + 1

Init ==
    /\ x = [i \in Procs |-> {0}]
    /\ y = [i \in Procs |-> 0]
    /\ pc = [i \in Procs |-> "write1"]

Write1(i) ==
    /\ pc[i] = "write1"
    /\ x' = [x EXCEPT ![i] = {0, 1}]
    /\ pc' = [pc EXCEPT ![i] = "write2"]
    /\ y' = y

Write2(i) ==
    /\ pc[i] = "write2"
    /\ x' = [x EXCEPT ![i] = {1}]
    /\ pc' = [pc EXCEPT ![i] = "read"]
    /\ y' = y

Read(i) ==
    /\ pc[i] = "read"
    /\ \E v \in x[Neighbor(i)]:
        /\ y' = [y EXCEPT ![i] = v]
        /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ x' = x

Next ==
    \E i \in Procs: Write1(i) \/ Write2(i) \/ Read(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK ==
    /\ x \in [Procs -> SUBSET {0, 1}]
    /\ y \in [Procs -> {0, 1}]
    /\ pc \in [Procs -> {"write1", "write2", "read", "done"}]

Terminated == \A i \in Procs: pc[i] = "done"

PCorrect == Terminated => \E i \in Procs: y[i] = 1

Inv ==
    /\ TypeOK
    /\ \A i \in Procs: pc[i] \in {"read", "done"} => 1 \in x[i]
    /\ \A i \in Procs: pc[i] = "done" /\ y[i] = 0 => 
        \E j \in Procs: j # i /\ pc[j] \in {"write1", "write2"}
    /\ \A i \in Procs: x[i] # {}

THEOREM InitImpliesInv == Init => Inv
<1>1. ASSUME Init
      PROVE TypeOK
  BY <1>1, NAssumption DEF Init, TypeOK, Procs
<1>2. ASSUME Init
      PROVE \A i \in Procs: pc[i] \in {"read", "done"} => 1 \in x[i]
  BY <1>2 DEF Init, Procs
<1>3. ASSUME Init
      PROVE \A i \in Procs: pc[i] = "done" /\ y[i] = 0 => 
            \E j \in Procs: j # i /\ pc[j] \in {"write1", "write2"}
  BY <1>3 DEF Init, Procs
<1>4. ASSUME Init
      PROVE \A i \in Procs: x[i] # {}
  BY <1>4 DEF Init, Procs
<1>. QED
  BY <1>1, <1>2, <1>3, <1>4 DEF Inv

THEOREM InvImpliesPCorrect == Inv => PCorrect
<1>1. ASSUME Inv, Terminated
      PROVE \E i \in Procs: y[i] = 1
  <2>1. \A i \in Procs: pc[i] = "done"
    BY <1>1 DEF Terminated
  <2>2. \A i \in Procs: pc[i] \notin {"write1", "write2"}
    BY <2>1
  <2>3. ASSUME \A i \in Procs: y[i] = 0
        PROVE FALSE
    <3>1. PICK i \in Procs: TRUE
      BY NAssumption DEF Procs
    <3>2. pc[i] = "done" /\ y[i] = 0
      BY <2>1, <2>3, <3>1
    <3>3. \E j \in Procs: j # i /\ pc[j] \in {"write1", "write2"}
      BY <3>2, <1>1 DEF Inv
    <3>. QED
      BY <3>3, <2>2
  <2>. QED
    BY <2>3, <1>1 DEF Inv, TypeOK, Procs
<1>. QED
  BY <1>1 DEF PCorrect

Termination == <>Terminated

=============================================================================