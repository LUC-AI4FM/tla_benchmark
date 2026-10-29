---- MODULE Session7Check ----
EXTENDS Naturals, TLC

\* Self-contained rendering of the imported Session7 specification:
\* two processes, "ProcA" and "ProcB", each atomically add 1 to a
\* shared variable x and then move to the "Done" control state.

Procs == {"ProcA", "ProcB"}

VARIABLES x, pc

vars == <<x, pc>>

Init ==
    /\ x = 0
    /\ pc = [p \in Procs |-> "Add"]

Add(p) ==
    /\ pc[p] = "Add"
    /\ x' = x + 1
    /\ pc' = [pc EXCEPT ![p] = "Done"]

Terminating ==
    /\ \A p \in Procs : pc[p] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Procs : Add(p)
    \/ Terminating

Spec == Init /\ [][Next]_vars

\* Correctness property: once both processes are done, x equals 2.
AddCorrect ==
    (pc["ProcA"] = "Done" /\ pc["ProcB"] = "Done") => x = 2

====