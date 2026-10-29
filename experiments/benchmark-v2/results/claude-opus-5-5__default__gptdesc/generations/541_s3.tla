---------------------------- MODULE Session7Check ----------------------------
EXTENDS Naturals, TLC

CONSTANTS ProcA, ProcB

ASSUME ProcA = "ProcA" /\ ProcB = "ProcB"

Procs == {"ProcA", "ProcB"}

VARIABLES x, tmp, pc

vars == << x, tmp, pc >>

TypeOK ==
    /\ x \in Nat
    /\ tmp \in [Procs -> Nat]
    /\ pc \in [Procs -> {"Read", "Write", "Done"}]

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

Termination == <>(\A p \in Procs : pc[p] = "Done")

\* Top-level correctness property (wrapper property over the imported spec)
AddCorrect ==
    (pc["ProcA"] = "Done" /\ pc["ProcB"] = "Done") => x = 2

=============================================================================