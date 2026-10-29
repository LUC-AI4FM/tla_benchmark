------------------------------ MODULE Fischer ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, Delta, Epsilon

ASSUME /\ N \in Nat \ {0}
       /\ Delta \in Nat \ {0}
       /\ Epsilon \in Nat \ {0}

Procs == 1..N

\* A timer value of Inactive means that the timer is not running.
Inactive == -1

VARIABLES x, pc, timer

vars == <<x, pc, timer>>

TypeOK ==
    /\ x \in {0} \cup Procs
    /\ pc \in [Procs -> {"ncs", "a", "b", "c", "cs"}]
    /\ timer \in [Procs -> {Inactive} \cup (0..(IF Delta > Epsilon THEN Delta ELSE Epsilon))]

Init ==
    /\ x = 0
    /\ pc = [p \in Procs |-> "ncs"]
    /\ timer = [p \in Procs |-> Inactive]

\* Leave the noncritical section and start trying.
Try(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "a"]
    /\ UNCHANGED <<x, timer>>

\* Wait until the shared variable is zero, then set the timer to Delta.
StepA(p) ==
    /\ pc[p] = "a"
    /\ x = 0
    /\ timer' = [timer EXCEPT ![p] = Delta]
    /\ pc' = [pc EXCEPT ![p] = "b"]
    /\ UNCHANGED x

\* Write own identifier into the shared variable (must happen before the
\* Delta timer expires), then set the timer to Epsilon.
StepB(p) ==
    /\ pc[p] = "b"
    /\ x' = p
    /\ timer' = [timer EXCEPT ![p] = Epsilon]
    /\ pc' = [pc EXCEPT ![p] = "c"]

\* Wait for the Epsilon timer to expire, then re-check the shared variable.
StepC(p) ==
    /\ pc[p] = "c"
    /\ timer[p] = 0
    /\ timer' = [timer EXCEPT ![p] = Inactive]
    /\ pc' = [pc EXCEPT ![p] = IF x = p THEN "cs" ELSE "a"]
    /\ UNCHANGED x

\* Leave the critical section, releasing the lock.
Exit(p) ==
    /\ pc[p] = "cs"
    /\ x' = 0
    /\ pc' = [pc EXCEPT ![p] = "ncs"]
    /\ UNCHANGED timer

Proc(p) == Try(p) \/ StepA(p) \/ StepB(p) \/ StepC(p) \/ Exit(p)

\* Global clock: decrements all active timers by one, but only when every
\* active timer is strictly positive.
Tick ==
    /\ \A p \in Procs : timer[p] = Inactive \/ timer[p] > 0
    /\ timer' = [p \in Procs |->
                    IF timer[p] = Inactive THEN Inactive ELSE timer[p] - 1]
    /\ UNCHANGED <<x, pc>>

Next == Tick \/ (\E p \in Procs : Proc(p))

Fairness == /\ \A p \in Procs : WF_vars(Proc(p))
            /\ WF_vars(Tick)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety: no two distinct processes are in the critical section at once.
\* Holds when Delta < Epsilon; violated when Delta >= Epsilon and N > 1.
MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

\* Liveness: some process enters the critical section infinitely often.
SomeoneInCS == \E p \in Procs : pc[p] = "cs"

Liveness == []<>SomeoneInCS

THEOREM Spec => [](TypeOK /\ MutualExclusion)
=============================================================================