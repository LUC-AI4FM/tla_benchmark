---- MODULE TurnMutex ----
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N > 0

Procs == 0 .. (N - 1)

VARIABLES turn, pc

vars == << turn, pc >>

TypeOK ==
    /\ turn \in Procs
    /\ pc \in [Procs -> {"ncs", "enter", "cs", "exit"}]

Init ==
    /\ turn \in Procs
    /\ pc = [p \in Procs |-> "ncs"]

NCS(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "enter"]
    /\ UNCHANGED turn

Enter(p) ==
    /\ pc[p] = "enter"
    /\ turn = p
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED turn

CS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED turn

Exit(p) ==
    /\ pc[p] = "exit"
    /\ turn' = (turn + 1) % N
    /\ pc' = [pc EXCEPT ![p] = "ncs"]

proc(p) == NCS(p) \/ Enter(p) \/ CS(p) \/ Exit(p)

Next == \E p \in Procs : proc(p)

Spec == Init /\ [][Next]_vars /\ \A p \in Procs : WF_vars(proc(p))

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

====