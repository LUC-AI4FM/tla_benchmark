---------------------------- MODULE MCSession7 ----------------------------
EXTENDS Naturals

\* Self-contained version of the Session7 model: two processes, ProcA and
\* ProcB, each perform a non-atomic increment of the shared variable x
\* (read into a local register, then write back register + 1).

Procs == {"ProcA", "ProcB"}

VARIABLES x, pc, t

vars == << x, pc, t >>

Init ==
    /\ x = 0
    /\ t = [p \in Procs |-> 0]
    /\ pc = [p \in Procs |-> "Read"]

Read(p) ==
    /\ pc[p] = "Read"
    /\ t' = [t EXCEPT ![p] = x]
    /\ pc' = [pc EXCEPT ![p] = "Write"]
    /\ UNCHANGED x

Write(p) ==
    /\ pc[p] = "Write"
    /\ x' = t[p] + 1
    /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ UNCHANGED t

Terminating ==
    /\ \A p \in Procs : pc[p] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Procs : Read(p) \/ Write(p)
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Invariant: once both processes are Done, x must equal 2.
AddCorrect ==
    (pc["ProcA"] = "Done" /\ pc["ProcB"] = "Done") => x = 2

=============================================================================