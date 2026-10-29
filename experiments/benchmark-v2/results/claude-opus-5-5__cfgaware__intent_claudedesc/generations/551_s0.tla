---- MODULE OneBitMutex ----
EXTENDS Integers, FiniteSets

CONSTANTS N, Procs

ConstN == 3
ConstProcs == 0 .. (ConstN - 1)

ASSUME N \in Nat /\ N > 0
ASSUME Procs = 0 .. (N - 1)

VARIABLES x, pc, j

vars == << x, pc, j >>

Trying == {"e1", "e2", "e3", "e4"}

TypeOK ==
    /\ x \in [Procs -> BOOLEAN]
    /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4", "cs", "exit"}]
    /\ j \in [Procs -> 0 .. N]

Init ==
    /\ x = [p \in Procs |-> FALSE]
    /\ pc = [p \in Procs |-> "ncs"]
    /\ j = [p \in Procs |-> 0]

\* Non-critical section: decide to enter
NCS(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "e1"]
    /\ UNCHANGED << x, j >>

\* Raise own flag and begin checking lower-numbered processes
E1(p) ==
    /\ pc[p] = "e1"
    /\ x' = [x EXCEPT ![p] = TRUE]
    /\ j' = [j EXCEPT ![p] = 0]
    /\ pc' = [pc EXCEPT ![p] = "e2"]

\* Check lower-numbered processes; back off if any has its flag set
E2(p) ==
    /\ pc[p] = "e2"
    /\ IF j[p] < p
         THEN IF x[j[p]]
                THEN /\ x' = [x EXCEPT ![p] = FALSE]
                     /\ pc' = [pc EXCEPT ![p] = "e3"]
                     /\ UNCHANGED j
                ELSE /\ j' = [j EXCEPT ![p] = j[p] + 1]
                     /\ UNCHANGED << x, pc >>
         ELSE /\ j' = [j EXCEPT ![p] = p + 1]
              /\ pc' = [pc EXCEPT ![p] = "e4"]
              /\ UNCHANGED x

\* Backed off: wait until the lower-numbered process lowers its flag, then retry
E3(p) ==
    /\ pc[p] = "e3"
    /\ ~x[j[p]]
    /\ pc' = [pc EXCEPT ![p] = "e1"]
    /\ UNCHANGED << x, j >>

\* Wait for each higher-numbered process to lower its flag
E4(p) ==
    /\ pc[p] = "e4"
    /\ IF j[p] >= N
         THEN /\ pc' = [pc EXCEPT ![p] = "cs"]
              /\ UNCHANGED << x, j >>
         ELSE /\ ~x[j[p]]
              /\ j' = [j EXCEPT ![p] = j[p] + 1]
              /\ UNCHANGED << x, pc >>

\* Critical section
CS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED << x, j >>

\* Exit protocol: lower own flag
Exit(p) ==
    /\ pc[p] = "exit"
    /\ x' = [x EXCEPT ![p] = FALSE]
    /\ pc' = [pc EXCEPT ![p] = "ncs"]
    /\ UNCHANGED j

Proc(p) == NCS(p) \/ E1(p) \/ E2(p) \/ E3(p) \/ E4(p) \/ CS(p) \/ Exit(p)

Next == \E p \in Procs : Proc(p)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A p \in Procs : WF_vars(Proc(p))

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

DeadAndLivelockFree ==
    (\E p \in Procs : pc[p] \in Trying) ~> (\E p \in Procs : pc[p] = "cs")

NoStarveProc0 ==
    (pc[0] \in Trying) ~> (pc[0] = "cs")

StarvationFree ==
    \A p \in Procs : (pc[p] \in Trying) ~> (pc[p] = "cs")

====