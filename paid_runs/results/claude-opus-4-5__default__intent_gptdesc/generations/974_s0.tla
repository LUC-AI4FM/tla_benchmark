---------------------------- MODULE RegularRegisters ----------------------------
EXTENDS Integers, FiniteSets, Naturals

CONSTANTS N

ASSUME N >= 1

Procs == 0..(N-1)

LeftNeighbor(p) == (p - 1) % N

ProgramCounters == {"idle", "writing", "written", "reading", "terminated"}

VARIABLES
    registers,
    localStorage,
    pc

vars == <<registers, localStorage, pc>>

TypeInvariant ==
    /\ \A p \in Procs : registers[p] \subseteq {0, 1}
    /\ \A p \in Procs : registers[p] /= {}
    /\ \A p \in Procs : localStorage[p] \in {0, 1}
    /\ \A p \in Procs : pc[p] \in ProgramCounters

Init ==
    /\ registers = [p \in Procs |-> {0}]
    /\ localStorage = [p \in Procs |-> 0]
    /\ pc = [p \in Procs |-> "idle"]

BeginWrite(p) ==
    /\ pc[p] = "idle"
    /\ registers' = [registers EXCEPT ![p] = registers[p] \union {1}]
    /\ pc' = [pc EXCEPT ![p] = "writing"]
    /\ UNCHANGED localStorage

CompleteWrite(p) ==
    /\ pc[p] = "writing"
    /\ registers' = [registers EXCEPT ![p] = {1}]
    /\ pc' = [pc EXCEPT ![p] = "written"]
    /\ UNCHANGED localStorage

BeginRead(p) ==
    /\ pc[p] = "written"
    /\ pc' = [pc EXCEPT ![p] = "reading"]
    /\ UNCHANGED <<registers, localStorage>>

CompleteRead(p) ==
    /\ pc[p] = "reading"
    /\ \E v \in registers[LeftNeighbor(p)] :
        /\ localStorage' = [localStorage EXCEPT ![p] = v]
        /\ pc' = [pc EXCEPT ![p] = "terminated"]
    /\ UNCHANGED registers

Next ==
    \E p \in Procs :
        \/ BeginWrite(p)
        \/ CompleteWrite(p)
        \/ BeginRead(p)
        \/ CompleteRead(p)

Fairness == \A p \in Procs :
    /\ WF_vars(BeginWrite(p))
    /\ WF_vars(CompleteWrite(p))
    /\ WF_vars(BeginRead(p))
    /\ WF_vars(CompleteRead(p))

Spec == Init /\ [][Next]_vars /\ Fairness

AllTerminated == \A p \in Procs : pc[p] = "terminated"

AtLeastOneReadOne == \E p \in Procs : localStorage[p] = 1

SafetyProperty ==
    AllTerminated => AtLeastOneReadOne

TerminationPossible == <>AllTerminated

=============================================================================