---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 2

Procs == 0..(N-1)

\* Fork indices for philosopher p
RightFork(p) == p
LeftFork(p)  == (p + 1) % N

VARIABLES pc, sem

vars == << pc, sem >>

Init ==
    /\ sem = [f \in Procs |-> TRUE]
    /\ pc  = [p \in Procs |-> "Lp"]

\* ---------------- Philosophers 1 .. N-1 : right fork, then left fork ----------

ThinkR(self) ==
    /\ self # 0
    /\ pc[self] = "Lp"
    /\ pc' = [pc EXCEPT ![self] = "R"]
    /\ UNCHANGED sem

TakeRightFirst(self) ==
    /\ self # 0
    /\ pc[self] = "R"
    /\ sem[RightFork(self)] = TRUE
    /\ sem' = [sem EXCEPT ![RightFork(self)] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "L"]

TakeLeftSecond(self) ==
    /\ self # 0
    /\ pc[self] = "L"
    /\ sem[LeftFork(self)] = TRUE
    /\ sem' = [sem EXCEPT ![LeftFork(self)] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "E"]

\* ---------------- Philosopher 0 : left fork, then right fork ------------------

ThinkL(self) ==
    /\ self = 0
    /\ pc[self] = "Lp"
    /\ pc' = [pc EXCEPT ![self] = "L"]
    /\ UNCHANGED sem

TakeLeftFirst(self) ==
    /\ self = 0
    /\ pc[self] = "L"
    /\ sem[LeftFork(self)] = TRUE
    /\ sem' = [sem EXCEPT ![LeftFork(self)] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "R"]

TakeRightSecond(self) ==
    /\ self = 0
    /\ pc[self] = "R"
    /\ sem[RightFork(self)] = TRUE
    /\ sem' = [sem EXCEPT ![RightFork(self)] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "E"]

\* ---------------- Eating and releasing forks (all philosophers) ---------------

EatAndRelease(self) ==
    /\ pc[self] = "E"
    /\ sem' = [sem EXCEPT ![RightFork(self)] = TRUE,
                          ![LeftFork(self)]  = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "Lp"]

\* ---------------- Process and global next-state relation ---------------------

proc(self) ==
    \/ ThinkR(self)
    \/ TakeRightFirst(self)
    \/ TakeLeftSecond(self)
    \/ ThinkL(self)
    \/ TakeLeftFirst(self)
    \/ TakeRightSecond(self)
    \/ EatAndRelease(self)

Next == \E self \in Procs : proc(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : SF_vars(proc(self))

\* ---------------- Properties --------------------------------------------------

TypeOK ==
    /\ pc  \in [Procs -> {"Lp", "R", "L", "E"}]
    /\ sem \in [Procs -> BOOLEAN]

Invariant ==
    \A i \in Procs : pc[i] = "E" => pc[(i + 1) % N] # "E"

StarvationFree ==
    \A i \in Procs : []<>(pc[i] = "E")

=============================================================================