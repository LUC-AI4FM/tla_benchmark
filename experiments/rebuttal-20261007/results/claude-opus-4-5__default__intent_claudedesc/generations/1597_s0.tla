---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT N

ASSUME N >= 1

VARIABLES x, y, b, pc

vars == <<x, y, b, pc>>

ProcSet == {1} \cup (2..N)

\* Process locations
\* "start" - initial state, ready to attempt entry
\* "set_flag" - setting own flag to TRUE
\* "write_x" - writing own id to x
\* "check_y" - checking if y is free
\* "write_y" - writing own id to y
\* "check_x" - checking if x still equals own id
\* "scan_flags" - scanning all flags (with scan index)
\* "wait_y" - waiting for y to become 0
\* "cs" - critical section
\* "exit" - exiting critical section

\* We use a record for pc to track both location and auxiliary state (scan index)
TypeOK ==
    /\ x \in 0..N
    /\ y \in 0..N
    /\ b \in [1..N -> BOOLEAN]
    /\ pc \in [ProcSet -> [loc: {"start", "set_flag", "write_x", "check_y", "write_y", 
                                  "check_x", "scan_flags", "wait_y", "cs", "exit"},
                           scan: 0..N]]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in 1..N |-> FALSE]
    /\ pc = [self \in ProcSet |-> [loc |-> "start", scan |-> 0]]

\* Process 1 actions (special process)
Start1 ==
    /\ pc[1].loc = "start"
    /\ pc' = [pc EXCEPT ![1].loc = "set_flag"]
    /\ UNCHANGED <<x, y, b>>

SetFlag1 ==
    /\ pc[1].loc = "set_flag"
    /\ b' = [b EXCEPT ![1] = TRUE]
    /\ pc' = [pc EXCEPT ![1].loc = "write_x"]
    /\ UNCHANGED <<x, y>>

WriteX1 ==
    /\ pc[1].loc = "write_x"
    /\ x' = 1
    /\ pc' = [pc EXCEPT ![1].loc = "check_y"]
    /\ UNCHANGED <<y, b>>

CheckY1 ==
    /\ pc[1].loc = "check_y"
    /\ IF y /= 0
       THEN pc' = [pc EXCEPT ![1].loc = "wait_y"]
       ELSE pc' = [pc EXCEPT ![1].loc = "write_y"]
    /\ UNCHANGED <<x, y, b>>

WriteY1 ==
    /\ pc[1].loc = "write_y"
    /\ y' = 1
    /\ pc' = [pc EXCEPT ![1].loc = "check_x"]
    /\ UNCHANGED <<x, b>>

CheckX1 ==
    /\ pc[1].loc = "check_x"
    /\ IF x /= 1
       THEN pc' = [pc EXCEPT ![1].loc = "scan_flags", ![1].scan = 1]
       ELSE pc' = [pc EXCEPT ![1].loc = "cs"]
    /\ UNCHANGED <<x, y, b>>

ScanFlags1 ==
    /\ pc[1].loc = "scan_flags"
    /\ IF pc[1].scan > N
       THEN pc' = [pc EXCEPT ![1].loc = "cs"]
       ELSE IF pc[1].scan /= 1 /\ b[pc[1].scan]
            THEN pc' = [pc EXCEPT ![1].loc = "wait_y"]
            ELSE pc' = [pc EXCEPT ![1].scan = pc[1].scan + 1]
    /\ UNCHANGED <<x, y, b>>

WaitY1 ==
    /\ pc[1].loc = "wait_y"
    /\ b' = [b EXCEPT ![1] = FALSE]
    /\ IF y = 0
       THEN pc' = [pc EXCEPT ![1].loc = "start"]
       ELSE IF y = 1
            THEN pc' = [pc EXCEPT ![1].loc = "cs"]
            ELSE pc' = [pc EXCEPT ![1].loc = "start"]
    /\ UNCHANGED <<x, y>>

CS1 ==
    /\ pc[1].loc = "cs"
    /\ pc' = [pc EXCEPT ![1].loc = "exit"]
    /\ UNCHANGED <<x, y, b>>

Exit1 ==
    /\ pc[1].loc = "exit"
    /\ y' = 0
    /\ b' = [b EXCEPT ![1] = FALSE]
    /\ pc' = [pc EXCEPT ![1].loc = "start"]
    /\ UNCHANGED <<x>>

Proc1 == Start1 \/ SetFlag1 \/ WriteX1 \/ CheckY1 \/ WriteY1 \/ 
         CheckX1 \/ ScanFlags1 \/ WaitY1 \/ CS1 \/ Exit1

\* Processes 2..N actions (parameterized group)
StartP(self) ==
    /\ self \in 2..N
    /\ pc[self].loc = "start"
    /\ pc' = [pc EXCEPT ![self].loc = "set_flag"]
    /\ UNCHANGED <<x, y, b>>

SetFlagP(self) ==
    /\ self \in 2..N
    /\ pc[self].loc = "set_flag"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self].loc = "write_x"]
    /\ UNCHANGED <<x, y>>

WriteXP(self) ==
    /\ self \in 2..N
    /\ pc[self].loc = "write_x"
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self].loc = "check_y"]
    /\ UNCHANGED <<y, b>>

CheckYP(self) ==
    /\ self \in 2..N
    /\ pc[self].loc = "check_y"
    /\ IF y /= 0
       THEN pc' = [pc EXCEPT ![self].loc = "wait_y"]
       ELSE pc' = [pc EXCEPT ![self].loc = "write_y"]
    /\ UNCHANGED <<x, y, b>>

WriteYP(self) ==
    /\ self \in 2..N
    /\ pc[self].loc = "write_y"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self].loc = "check_x"]
    /\ UNCHANGED <<x, b>>

CheckXP(self) ==
    /\ self \in 2..N
    /\ pc[self].loc = "check_x"
    /\ IF x /= self
       THEN pc' = [pc EXCEPT ![self].loc = "scan_flags", ![self].scan = 1]
       ELSE pc' = [pc EXCEPT ![self].loc = "cs"]
    /\ UNCHANGED <<x, y, b>>

ScanFlagsP(self) ==
    /\ self \in 2..N
    /\ pc[self].loc = "scan_flags"
    /\ IF pc[self].scan > N
       THEN pc' = [pc EXCEPT ![self].loc = "cs"]
       ELSE IF pc[self].scan /= self /\ b[pc[self].scan]
            THEN pc' = [pc EXCEPT ![self].loc = "wait_y"]
            ELSE pc' = [pc EXCEPT ![self].scan = pc[self].scan + 1]
    /\ UNCHANGED <<x, y, b>>

WaitYP(self) ==
    /\ self \in 2..N
    /\ pc[self].loc = "wait_y"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ IF y = 0
       THEN pc' = [pc EXCEPT ![self].loc = "start"]
       ELSE IF y = self
            THEN pc' = [pc EXCEPT ![self].loc = "cs"]
            ELSE pc' = [pc EXCEPT ![self].loc = "start"]
    /\ UNCHANGED <<x, y>>

CSP(self) ==
    /\ self \in 2..N
    /\ pc[self].loc = "cs"
    /\ pc' = [pc EXCEPT ![self].loc = "exit"]
    /\ UNCHANGED <<x, y, b>>

ExitP(self) ==
    /\ self \in 2..N
    /\ pc[self].loc = "exit"
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self].loc = "start"]
    /\ UNCHANGED <<x>>

ProcP(self) == StartP(self) \/ SetFlagP(self) \/ WriteXP(self) \/ CheckYP(self) \/ 
               WriteYP(self) \/ CheckXP(self) \/ ScanFlagsP(self) \/ WaitYP(self) \/ 
               CSP(self) \/ ExitP(self)

Next == Proc1 \/ (\E self \in 2..N : ProcP(self))

\* Fairness: weak fairness for all processes
Fairness == 
    /\ WF_vars(Proc1)
    /\ \A self \in 2..N : WF_vars(ProcP(self))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: Mutual Exclusion - no two distinct processes in CS simultaneously
InCS(p) == pc[p].loc = "cs"

MutualExclusion == \A p, q \in ProcSet : (p /= q) => ~(InCS(p) /\ InCS(q))

\* Liveness: some process reaches CS infinitely often
SomeoneInCS == \E p \in ProcSet : InCS(p)

Liveness == []<>SomeoneInCS

==========================================================================