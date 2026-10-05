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

\* Process i begins writing 1 to x[i]: transition from {0} to {0,1}
Write1(i) ==
    /\ pc[i] = "write1"
    /\ x' = [x EXCEPT ![i] = {0, 1}]
    /\ y' = y
    /\ pc' = [pc EXCEPT ![i] = "write2"]

\* Process i completes writing 1 to x[i]: transition from {0,1} to {1}
Write2(i) ==
    /\ pc[i] = "write2"
    /\ x' = [x EXCEPT ![i] = {1}]
    /\ y' = y
    /\ pc' = [pc EXCEPT ![i] = "read"]

\* Neighbor function: process i reads from process (i mod N) + 1
Neighbor(i) == (i % N) + 1

\* Process i reads neighbor's register, getting any value in the set
Read(i) ==
    /\ pc[i] = "read"
    /\ \E v \in x[Neighbor(i)] :
        /\ y' = [y EXCEPT ![i] = v]
        /\ x' = x
        /\ pc' = [pc EXCEPT ![i] = "done"]

\* Process i has terminated
Done(i) ==
    /\ pc[i] = "done"
    /\ UNCHANGED vars

Next ==
    \/ \E i \in Procs : Write1(i)
    \/ \E i \in Procs : Write2(i)
    \/ \E i \in Procs : Read(i)
    \/ \E i \in Procs : Done(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Termination condition
Terminated == \A i \in Procs : pc[i] = "done"

\* Type correctness invariant
TypeOK ==
    /\ x \in [Procs -> SUBSET {0, 1}]
    /\ \A i \in Procs : x[i] # {}
    /\ y \in [Procs -> {0, 1}]
    /\ pc \in [Procs -> {"write1", "write2", "read", "done"}]

\* Safety property: if all processes are done, some y[i] = 1
PCorrect == Terminated => \E i \in Procs : y[i] = 1

\* Key observation: once a process passes write1, its register contains 1
PastWrite1(i) == pc[i] \in {"write2", "read", "done"}

\* Inductive invariant
Inv ==
    /\ TypeOK
    /\ \A i \in Procs : PastWrite1(i) => 1 \in x[i]
    /\ \A i \in Procs : (pc[i] = "done" /\ y[i] = 0) => 
                        \E j \in Procs : pc[j] = "write1"

\* Proof that Inv is an inductive invariant
THEOREM InvInductive == Spec => []Inv
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK, PastWrite1, Procs
<1>2. Inv /\ [Next]_vars => Inv'
  <2>1. ASSUME Inv, Next PROVE Inv'
    BY DEF Inv, TypeOK, Next, Write1, Write2, Read, Done, PastWrite1, Procs, Neighbor, vars
  <2>2. ASSUME Inv, UNCHANGED vars PROVE Inv'
    BY DEF Inv, TypeOK, PastWrite1, vars
  <2>3. QED BY <2>1, <2>2
<1>3. QED BY <1>1, <1>2, PTL DEF Spec

\* Proof that Inv implies PCorrect
THEOREM Safety == Spec => []PCorrect
<1>1. Inv => PCorrect
  BY DEF Inv, PCorrect, Terminated, TypeOK, PastWrite1, Procs
<1>2. QED BY <1>1, InvInductive, PTL

=============================================================================