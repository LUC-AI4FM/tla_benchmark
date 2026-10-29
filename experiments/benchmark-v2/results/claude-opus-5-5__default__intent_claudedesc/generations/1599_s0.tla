---------------------------- MODULE FastMutex ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssump == N \in Nat /\ N > 0

ProcSet == 1..N

VARIABLES x, y, b, j, pc

vars == << x, y, b, j, pc >>

TypeOK ==
    /\ x \in 0..N
    /\ y \in 0..N
    /\ b \in [ProcSet -> BOOLEAN]
    /\ j \in [ProcSet -> 0..(N+1)]
    /\ pc \in [ProcSet -> {"ncs", "start", "l1", "l2", "l3", "l4", "l5",
                           "l6", "l7", "l8", "l9", "l10", "cs", "l11", "l12"}]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in ProcSet |-> FALSE]
    /\ j = [i \in ProcSet |-> 0]
    /\ pc = [i \in ProcSet |-> "ncs"]

\* Non-critical section: the process may stay here forever.
ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, j >>

\* Announce interest.
start(self) ==
    /\ pc[self] = "start"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "l1"]
    /\ UNCHANGED << x, y, j >>

\* x := self
l1(self) ==
    /\ pc[self] = "l1"
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "l2"]
    /\ UNCHANGED << y, b, j >>

\* if y # 0 then back off, else continue
l2(self) ==
    /\ pc[self] = "l2"
    /\ IF y # 0
          THEN pc' = [pc EXCEPT ![self] = "l3"]
          ELSE pc' = [pc EXCEPT ![self] = "l5"]
    /\ UNCHANGED << x, y, b, j >>

\* b[self] := FALSE
l3(self) ==
    /\ pc[self] = "l3"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "l4"]
    /\ UNCHANGED << x, y, j >>

\* await y = 0; goto start
l4(self) ==
    /\ pc[self] = "l4"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, j >>

\* y := self
l5(self) ==
    /\ pc[self] = "l5"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "l6"]
    /\ UNCHANGED << x, b, j >>

\* if x # self then slow path, else enter CS (fast path)
l6(self) ==
    /\ pc[self] = "l6"
    /\ IF x # self
          THEN pc' = [pc EXCEPT ![self] = "l7"]
          ELSE pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED << x, y, b, j >>

\* b[self] := FALSE; j := 1
l7(self) ==
    /\ pc[self] = "l7"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ j' = [j EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "l8"]
    /\ UNCHANGED << x, y >>

\* while j <= N do await ~b[j]; j := j + 1 od
l8(self) ==
    /\ pc[self] = "l8"
    /\ IF j[self] <= N
          THEN /\ ~b[j[self]]
               /\ j' = [j EXCEPT ![self] = j[self] + 1]
               /\ pc' = [pc EXCEPT ![self] = "l8"]
          ELSE /\ pc' = [pc EXCEPT ![self] = "l9"]
               /\ UNCHANGED j
    /\ UNCHANGED << x, y, b >>

\* if y # self then wait and retry, else enter CS
l9(self) ==
    /\ pc[self] = "l9"
    /\ IF y # self
          THEN pc' = [pc EXCEPT ![self] = "l10"]
          ELSE pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED << x, y, b, j >>

\* await y = 0; goto start
l10(self) ==
    /\ pc[self] = "l10"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, j >>

\* Critical section
cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "l11"]
    /\ UNCHANGED << x, y, b, j >>

\* y := 0
l11(self) ==
    /\ pc[self] = "l11"
    /\ y' = 0
    /\ pc' = [pc EXCEPT ![self] = "l12"]
    /\ UNCHANGED << x, b, j >>

\* b[self] := FALSE; goto ncs
l12(self) ==
    /\ pc[self] = "l12"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED << x, y, j >>

\* All protocol steps (excluding the non-critical section step)
ProtocolStep(self) ==
    \/ start(self) \/ l1(self) \/ l2(self) \/ l3(self) \/ l4(self)
    \/ l5(self) \/ l6(self) \/ l7(self) \/ l8(self) \/ l9(self)
    \/ l10(self) \/ cs(self) \/ l11(self) \/ l12(self)

proc(self) == ncs(self) \/ ProtocolStep(self)

Next == \E self \in ProcSet : proc(self)

Fairness ==
    \A self \in ProcSet :
        /\ WF_vars(start(self))
        /\ WF_vars(l1(self))
        /\ WF_vars(l2(self))
        /\ WF_vars(l3(self))
        /\ WF_vars(l4(self))
        /\ WF_vars(l5(self))
        /\ WF_vars(l6(self))
        /\ WF_vars(l7(self))
        /\ WF_vars(l8(self))
        /\ WF_vars(l9(self))
        /\ WF_vars(l10(self))
        /\ WF_vars(cs(self))
        /\ WF_vars(l11(self))
        /\ WF_vars(l12(self))

Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
\* Safety: mutual exclusion
MutualExclusion ==
    \A p, q \in ProcSet : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

\* Liveness: if some process eventually stays out of its non-critical
\* section forever (keeps trying), then some process enters the critical
\* section infinitely often.
Liveness ==
    (\E i \in ProcSet : <>[](pc[i] # "ncs"))
        => []<>(\E i \in ProcSet : pc[i] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => Liveness
=============================================================================