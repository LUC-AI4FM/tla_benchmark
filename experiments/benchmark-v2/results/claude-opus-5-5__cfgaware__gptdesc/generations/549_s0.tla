---------------------------- MODULE MCSession9alt ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, Procs

ASSUME N \in Nat /\ N >= 1

VARIABLES pc, lock

vars == << pc, lock >>

-----------------------------------------------------------------------------
\* Concrete model values for the constants.

ConstN == 3

ConstProcs == 1..ConstN

-----------------------------------------------------------------------------
\* Stand-in for the algorithm that the original module inherits from
\* Session9alt. It is a simple lock-based mutual exclusion protocol over pc.

Init ==
    /\ pc = [p \in Procs |-> "ncs"]
    /\ lock = FALSE

Enter(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "try"]
    /\ UNCHANGED lock

Acquire(p) ==
    /\ pc[p] = "try"
    /\ lock = FALSE
    /\ lock' = TRUE
    /\ pc' = [pc EXCEPT ![p] = "cs"]

Exit(p) ==
    /\ pc[p] = "cs"
    /\ lock' = FALSE
    /\ pc' = [pc EXCEPT ![p] = "ncs"]

Next ==
    \E p \in Procs : Enter(p) \/ Acquire(p) \/ Exit(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in Procs :
        /\ WF_vars(Enter(p))
        /\ WF_vars(Exit(p))
        /\ SF_vars(Acquire(p))

-----------------------------------------------------------------------------
\* Properties

\* Safety: no two distinct processes are in the critical section at once.
MutualExclusion ==
    [](\A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs"))

\* Naive liveness: every process visits the critical section infinitely often.
LivenessNaive ==
    \A p \in Procs : []<>(pc[p] = "cs")

=============================================================================