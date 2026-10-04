---------------------------- MODULE specification ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 0

VARIABLES
    reg,      \* reg[i] is a set of values that can be read from process i's register
    writing,  \* writing[i] is the value currently being written by process i (or -1 if not writing)
    local,    \* local[i] is the value read by process i from its left neighbor
    pc        \* pc[i] is the program counter of process i

vars == <<reg, writing, local, pc>>

Procs == 0..(N-1)

LeftNeighbor(i) == (i + N - 1) % N

\* Program counter states:
\* "idle"      - initial state, ready to begin writing
\* "writing"   - write in progress (begun but not completed)
\* "written"   - write completed, ready to read
\* "reading"   - read in progress
\* "done"      - terminated

PCStates == {"idle", "writing", "written", "reading", "done"}

TypeOK ==
    /\ reg \in [Procs -> SUBSET {0, 1}]
    /\ \A i \in Procs : reg[i] # {}
    /\ writing \in [Procs -> {-1, 0, 1}]
    /\ local \in [Procs -> {0, 1}]
    /\ \A i \in Procs : pc[i] \in PCStates

Init ==
    /\ reg = [i \in Procs |-> {0}]
    /\ writing = [i \in Procs |-> -1]
    /\ local = [i \in Procs |-> 0]
    /\ pc = [i \in Procs |-> "idle"]

\* Process i begins writing value 1 to its register
\* The register now can return either old value or new value (regular semantics)
BeginWrite(i) ==
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "writing"]
    /\ writing' = [writing EXCEPT ![i] = 1]
    /\ reg' = [reg EXCEPT ![i] = reg[i] \union {1}]  \* Add new value to possible reads
    /\ UNCHANGED local

\* Process i completes writing value 1 to its register
\* After completion, only the written value remains
EndWrite(i) ==
    /\ pc[i] = "writing"
    /\ pc' = [pc EXCEPT ![i] = "written"]
    /\ writing' = [writing EXCEPT ![i] = -1]
    /\ reg' = [reg EXCEPT ![i] = {1}]  \* Write completes, only final value available
    /\ UNCHANGED local

\* Process i begins reading from its left neighbor
BeginRead(i) ==
    /\ pc[i] = "written"
    /\ pc' = [pc EXCEPT ![i] = "reading"]
    /\ UNCHANGED <<reg, writing, local>>

\* Process i completes reading from its left neighbor
\* Regular register semantics: can read any value in the neighbor's reg set
EndRead(i) ==
    /\ pc[i] = "reading"
    /\ \E v \in reg[LeftNeighbor(i)] :
        /\ local' = [local EXCEPT ![i] = v]
        /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<reg, writing>>

Next ==
    \E i \in Procs :
        \/ BeginWrite(i)
        \/ EndWrite(i)
        \/ BeginRead(i)
        \/ EndRead(i)

Fairness == \A i \in Procs :
    /\ WF_vars(BeginWrite(i))
    /\ WF_vars(EndWrite(i))
    /\ WF_vars(BeginRead(i))
    /\ WF_vars(EndRead(i))

Spec == Init /\ [][Next]_vars /\ Fairness

\* All processes have terminated
AllTerminated == \A i \in Procs : pc[i] = "done"

\* At least one process read value 1
SomeReadOne == \E i \in Procs : local[i] = 1

\* Safety property: if all terminate, at least one read 1
Inv == AllTerminated => SomeReadOne

\* Progress property: it is possible for all processes to eventually terminate
\* This is expressed as a liveness property
PCorrect == <>AllTerminated

=============================================================================