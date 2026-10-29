---- MODULE TurnMutex ----
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

Procs == 0 .. N-1

VARIABLES turn, pc

vars == <<turn, pc>>

Init ==
    /\ turn \in Procs
    /\ pc = [p \in Procs |-> "ncs"]

NonCritical(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "enter"]
    /\ UNCHANGED turn

Enter(p) ==
    /\ pc[p] = "enter"
    /\ turn = p
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED turn

Critical(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED turn

Exit(p) ==
    /\ pc[p] = "exit"
    /\ turn' = (turn + 1) % N
    /\ pc' = [pc EXCEPT ![p] = "ncs"]

Proc(p) ==
    \/ NonCritical(p)
    \/ Enter(p)
    \/ Critical(p)
    \/ Exit(p)

Next == \E p \in Procs : Proc(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ turn \in Procs
    /\ pc \in [Procs -> {"ncs", "enter", "cs", "exit"}]

====