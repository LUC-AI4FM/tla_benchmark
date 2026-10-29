---------------------------- MODULE ConcurrentIncrement ----------------------------
EXTENDS Naturals, TLC

Procs == {1, 2}

VARIABLES x, tmp, pc

vars == << x, tmp, pc >>

Init ==
    /\ x = 0
    /\ tmp = [p \in Procs |-> 0]
    /\ pc = [p \in Procs |-> "Read"]

Read(p) ==
    /\ pc[p] = "Read"
    /\ tmp' = [tmp EXCEPT ![p] = x]
    /\ pc' = [pc EXCEPT ![p] = "Write"]
    /\ UNCHANGED x

Write(p) ==
    /\ pc[p] = "Write"
    /\ x' = tmp[p] + 1
    /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ UNCHANGED tmp

Proc(p) == Read(p) \/ Write(p)

Terminating ==
    /\ \A p \in Procs : pc[p] = "Done"
    /\ UNCHANGED vars

Next == (\E p \in Procs : Proc(p)) \/ Terminating

Spec == Init /\ [][Next]_vars /\ \A p \in Procs : WF_vars(Proc(p))

TypeOK ==
    /\ x \in Nat
    /\ tmp \in [Procs -> Nat]
    /\ pc \in [Procs -> {"Read", "Write", "Done"}]

AddCorrect == (\A p \in Procs : pc[p] = "Done") => (x = 2)

=============================================================================