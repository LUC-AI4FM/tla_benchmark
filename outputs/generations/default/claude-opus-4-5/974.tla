---------------------------- MODULE RegularReaders ----------------------------
EXTENDS Naturals, FiniteSets, TLAPS

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES x, y, pc

vars == <<x, y, pc>>

Procs == 1..N

Init == 
    /\ x = [i \in Procs |-> {0}]
    /\ y = [i \in Procs |-> 0]
    /\ pc = [i \in Procs |-> "write1"]

\* Process i begins writing 1 to x[i] - models start of write (0 -> {0,1})
Write1Start(i) ==
    /\ pc[i] = "write1"
    /\ x' = [x EXCEPT ![i] = {0, 1}]
    /\ pc' = [pc EXCEPT ![i] = "write2"]
    /\ y' = y

\* Process i completes writing 1 to x[i] - models end of write ({0,1} -> {1})
Write2Complete(i) ==
    /\ pc[i] = "write2"
    /\ x' = [x EXCEPT ![i] = {1}]
    /\ pc' = [pc EXCEPT ![i] = "read"]
    /\ y' = y

\* Neighbor function: process i reads from neighbor (i mod N) + 1
Neighbor(i) == (i % N) + 1

\* Process i reads from neighbor's register - may read any value in the set
Read(i) ==
    /\ pc[i] = "read"
    /\ \E v \in x[Neighbor(i)] : y' = [y EXCEPT ![i] = v]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ x' = x

\* Next state relation
Next == \E i \in Procs : Write1Start(i) \/ Write2Complete(i) \/ Read(i)

\* Fairness: weak fairness on all actions
Fairness == \A i \in Procs : 
    /\ WF_vars(Write1Start(i))
    /\ WF_vars(Write2Complete(i))
    /\ WF_vars(Read(i))

\* Specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* Termination: all processes reach done state
Termination == \A i \in Procs : pc[i] = "done"

\* Safety property: if all processes are done, some y[i] equals 1
PCorrect == Termination => \E i \in Procs : y[i] = 1

\* Type invariant
TypeOK ==
    /\ x \in [Procs -> SUBSET {0, 1}]
    /\ y \in [Procs -> {0, 1}]
    /\ pc \in [Procs -> {"write1", "write2", "read", "done"}]

\* Key observation: once a process leaves write1, its x contains 1
WrittenImpliesOne == \A i \in Procs : pc[i] \in {"write2", "read", "done"} => 1 \in x[i]

\* Once a process is done writing (in read or done), x[i] = {1}
DoneWritingImpliesOnlyOne == \A i \in Procs : pc[i] \in {"read", "done"} => x[i] = {1}

\* The last process to read must see a 1
\* If process i is done and read 0, its neighbor must have started writing before i read
LastReaderSeesOne == 
    \A i \in Procs : 
        (pc[i] = "done" /\ y[i] = 0) => 
        (pc[Neighbor(i)] \in {"write2", "read", "done"})

\* Inductive invariant
Inv == 
    /\ TypeOK
    /\ WrittenImpliesOne
    /\ DoneWritingImpliesOnlyOne
    /\ \A i \in Procs : x[i] # {}
    /\ \A i \in Procs : (pc[i] = "done" /\ y[i] = 0) => 
                        (pc[Neighbor(i)] \in {"read", "done"})
    /\ Termination => \E i \in Procs : y[i] = 1

\* THEOREM: Invariant implies safety property
THEOREM InvImpliesSafety == Inv => PCorrect
<1>1. Inv => PCorrect
  BY DEF Inv, PCorrect, Termination
<1>. QED BY <1>1

\* THEOREM: Specification satisfies safety
THEOREM Safety == Spec => []PCorrect
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK, WrittenImpliesOne, DoneWritingImpliesOnlyOne, 
         Termination, Procs, NAssumption
<1>2. Inv /\ [Next]_vars => Inv'
  <2>1. ASSUME Inv, Next PROVE Inv'
    BY <2>1 DEF Inv, Next, Write1Start, Write2Complete, Read, TypeOK,
           WrittenImpliesOne, DoneWritingImpliesOnlyOne, Termination,
           Procs, Neighbor, vars, NAssumption
  <2>2. ASSUME Inv, UNCHANGED vars PROVE Inv'
    BY <2>2 DEF Inv, vars, TypeOK, WrittenImpliesOne, DoneWritingImpliesOnlyOne,
           Termination, Procs
  <2>. QED BY <2>1, <2>2
<1>3. Inv => PCorrect
  BY DEF Inv, PCorrect, Termination
<1>. QED BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================