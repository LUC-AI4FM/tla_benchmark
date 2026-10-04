---------------------------- MODULE RegularReaders ----------------------------
EXTENDS Integers, FiniteSets, TLAPS

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES x, y, pc

vars == <<x, y, pc>>

Procs == 1..N

TypeOK == /\ x \in [Procs -> SUBSET {0, 1}]
          /\ y \in [Procs -> {0, 1}]
          /\ pc \in [Procs -> {"write1", "write2", "read", "done"}]

Init == /\ x = [i \in Procs |-> {0}]
        /\ y = [i \in Procs |-> 0]
        /\ pc = [i \in Procs |-> "write1"]

Neighbor(i) == IF i = N THEN 1 ELSE i + 1

Write1(i) == /\ pc[i] = "write1"
             /\ x' = [x EXCEPT ![i] = {0, 1}]
             /\ pc' = [pc EXCEPT ![i] = "write2"]
             /\ y' = y

Write2(i) == /\ pc[i] = "write2"
             /\ x' = [x EXCEPT ![i] = {1}]
             /\ pc' = [pc EXCEPT ![i] = "read"]
             /\ y' = y

Read(i) == /\ pc[i] = "read"
           /\ \E v \in x[Neighbor(i)] : y' = [y EXCEPT ![i] = v]
           /\ pc' = [pc EXCEPT ![i] = "done"]
           /\ x' = x

Done(i) == /\ pc[i] = "done"
           /\ UNCHANGED vars

Next == \E i \in Procs : Write1(i) \/ Write2(i) \/ Read(i) \/ Done(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (\A i \in Procs : pc[i] = "done")

AllDone == \A i \in Procs : pc[i] = "done"

PCorrect == AllDone => \E i \in Procs : y[i] = 1

Inv == /\ TypeOK
       /\ \A i \in Procs : pc[i] \in {"read", "done"} => 1 \in x[i]
       /\ \A i \in Procs : pc[i] = "done" /\ y[i] = 0 => 
            (pc[Neighbor(i)] \in {"write1", "write2"})
       /\ \A i \in Procs : 0 \in x[i] => pc[i] \in {"write1", "write2"}
       /\ \A i \in Procs : pc[i] = "write2" => x[i] = {0, 1}
       /\ \A i \in Procs : pc[i] = "write1" => x[i] = {0}

THEOREM InitImpliesInv == Init => Inv
<1>1. ASSUME Init
      PROVE  Inv
  <2>1. TypeOK
    BY <1>1 DEF Init, TypeOK, Procs
  <2>2. \A i \in Procs : pc[i] \in {"read", "done"} => 1 \in x[i]
    BY <1>1 DEF Init, Procs
  <2>3. \A i \in Procs : pc[i] = "done" /\ y[i] = 0 => 
          (pc[Neighbor(i)] \in {"write1", "write2"})
    BY <1>1 DEF Init, Procs
  <2>4. \A i \in Procs : 0 \in x[i] => pc[i] \in {"write1", "write2"}
    BY <1>1 DEF Init, Procs
  <2>5. \A i \in Procs : pc[i] = "write2" => x[i] = {0, 1}
    BY <1>1 DEF Init, Procs
  <2>6. \A i \in Procs : pc[i] = "write1" => x[i] = {0}
    BY <1>1 DEF Init, Procs
  <2>7. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Inv
<1>2. QED
  BY <1>1

THEOREM InvImpliesPCorrect == Inv => PCorrect
<1>1. ASSUME Inv, AllDone
      PROVE  \E i \in Procs : y[i] = 1
  <2>1. PICK i \in Procs : TRUE
    BY NAssumption DEF Procs
  <2>2. pc[i] = "done"
    BY <1>1 DEF AllDone
  <2>3. pc[Neighbor(i)] = "done"
    BY <1>1 DEF AllDone, Neighbor, Procs, NAssumption
  <2>4. pc[Neighbor(i)] \notin {"write1", "write2"}
    BY <2>3
  <2>5. ~(pc[i] = "done" /\ y[i] = 0)
    BY <1>1, <2>4 DEF Inv
  <2>6. y[i] = 1
    BY <1>1, <2>2, <2>5 DEF Inv, TypeOK
  <2>7. QED
    BY <2>1, <2>6
<1>2. QED
  BY <1>1 DEF PCorrect

Safety == []PCorrect

Liveness == Termination

===============================================================================