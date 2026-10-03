---------------------------- MODULE RegularRegisters ----------------------------
EXTENDS Integers, FiniteSets, TLAPS

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES x, y, pc

vars == <<x, y, pc>>

Procs == 1..N

Init ==
    /\ x = [i \in Procs |-> {0}]
    /\ y = [i \in Procs |-> 0]
    /\ pc = [i \in Procs |-> "write1"]

\* Process i begins writing 1 to x[i] - first step makes it {0,1}
Write1(i) ==
    /\ pc[i] = "write1"
    /\ x' = [x EXCEPT ![i] = {0, 1}]
    /\ y' = y
    /\ pc' = [pc EXCEPT ![i] = "write2"]

\* Process i completes writing 1 to x[i] - second step makes it {1}
Write2(i) ==
    /\ pc[i] = "write2"
    /\ x' = [x EXCEPT ![i] = {1}]
    /\ y' = y
    /\ pc' = [pc EXCEPT ![i] = "read"]

\* Process i reads neighbor's register (circular neighbor: i mod N + 1)
\* Read can return any value in the set
Read(i) ==
    /\ pc[i] = "read"
    /\ \E v \in x[(i % N) + 1] : y' = [y EXCEPT ![i] = v]
    /\ x' = x
    /\ pc' = [pc EXCEPT ![i] = "done"]

Next ==
    \E i \in Procs : Write1(i) \/ Write2(i) \/ Read(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == \A i \in Procs : pc[i] = "done"

\* Safety property: if all processes are done, some y[i] equals 1
PCorrect == Termination => \E i \in Procs : y[i] = 1

TypeOK ==
    /\ x \in [Procs -> SUBSET {0, 1}]
    /\ y \in [Procs -> {0, 1}]
    /\ pc \in [Procs -> {"write1", "write2", "read", "done"}]

\* Inductive invariant: 
\* - Type correctness
\* - If a process is past write2, its register contains 1
\* - If a process has read and got 0, its neighbor hadn't finished writing yet
\* - Key insight: at least one process will see a 1
Inv ==
    /\ TypeOK
    /\ \A i \in Procs : pc[i] \in {"read", "done"} => 1 \in x[i]
    /\ \A i \in Procs : pc[i] = "done" /\ y[i] = 0 => 
         pc[(i % N) + 1] \in {"write1", "write2"}
    /\ \A i \in Procs : x[i] # {}

\* THEOREM 1: Invariant implies safety property
THEOREM InvImpliesSafety == Inv => PCorrect
<1>1. SUFFICES ASSUME Inv, Termination
      PROVE \E i \in Procs : y[i] = 1
      BY DEF PCorrect
<1>2. \A i \in Procs : pc[i] = "done"
      BY <1>1 DEF Termination
<1>3. \A i \in Procs : y[i] = 0 => pc[(i % N) + 1] \in {"write1", "write2"}
      BY <1>1 DEF Inv
<1>4. \A i \in Procs : pc[(i % N) + 1] = "done"
      BY <1>2, NAssumption DEF Procs
<1>5. \A i \in Procs : ~(y[i] = 0)
      BY <1>3, <1>4
<1>6. \A i \in Procs : y[i] \in {0, 1}
      BY <1>1 DEF Inv, TypeOK
<1>7. N >= 1
      BY NAssumption
<1>8. 1 \in Procs
      BY <1>7 DEF Procs
<1>9. y[1] = 1
      BY <1>5, <1>6, <1>8
<1>10. QED
      BY <1>8, <1>9

\* THEOREM 2: Invariant is inductive
THEOREM InvInductive == Init => Inv
<1>1. SUFFICES ASSUME Init PROVE Inv
      OBVIOUS
<1>2. x = [i \in Procs |-> {0}]
      BY <1>1 DEF Init
<1>3. y = [i \in Procs |-> 0]
      BY <1>1 DEF Init
<1>4. pc = [i \in Procs |-> "write1"]
      BY <1>1 DEF Init
<1>5. TypeOK
      BY <1>2, <1>3, <1>4 DEF TypeOK, Procs
<1>6. \A i \in Procs : pc[i] \in {"read", "done"} => 1 \in x[i]
      BY <1>4 DEF Procs
<1>7. \A i \in Procs : pc[i] = "done" /\ y[i] = 0 => 
         pc[(i % N) + 1] \in {"write1", "write2"}
      BY <1>4 DEF Procs
<1>8. \A i \in Procs : x[i] # {}
      BY <1>2 DEF Procs
<1>9. QED
      BY <1>5, <1>6, <1>7, <1>8 DEF Inv

=============================================================================