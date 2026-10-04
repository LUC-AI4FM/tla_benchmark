---------------------------- MODULE TerminationDetection ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 0

VARIABLES
    active,
    terminated

vars == <<active, terminated>>

Procs == 1..N

TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ terminated \in BOOLEAN

Init ==
    /\ active \in [Procs -> BOOLEAN]
    /\ terminated = FALSE

AllInactive == \A p \in Procs : ~active[p]

LocalTerminate(p) ==
    /\ active[p]
    /\ ~terminated
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ UNCHANGED terminated

Activate(p, q) ==
    /\ p # q
    /\ active[p]
    /\ ~terminated
    /\ active' = [active EXCEPT ![q] = TRUE]
    /\ UNCHANGED terminated

DetectTermination ==
    /\ AllInactive
    /\ ~terminated
    /\ terminated' = TRUE
    /\ UNCHANGED active

Next ==
    \/ \E p \in Procs : LocalTerminate(p)
    \/ \E p, q \in Procs : Activate(p, q)
    \/ DetectTermination

Fairness == WF_vars(DetectTermination)

Spec == Init /\ [][Next]_vars /\ Fairness

Safety == terminated => AllInactive

QuiescencePersistence == [][AllInactive => AllInactive']_vars

Liveness == AllInactive ~> terminated

=============================================================================