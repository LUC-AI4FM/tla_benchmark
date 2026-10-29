---------------------------- MODULE Peterson ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N >= 1

Procs == 0..(N-1)

Levels == 0..(N-2)

VARIABLES level, last_to_enter, pc, l

vars == << level, last_to_enter, pc, l >>

TypeOK ==
    /\ level \in [Procs -> -1..(N-2)]
    /\ last_to_enter \in [Levels -> Procs]
    /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "cs", "exit_cs"}]
    /\ l \in [Procs -> 0..(N-1)]

Init ==
    /\ level = [p \in Procs |-> -1]
    /\ last_to_enter = [x \in Levels |-> 0]
    /\ pc = [p \in Procs |-> "ncs"]
    /\ l = [p \in Procs |-> 0]

ncs(self) ==
    /\ pc[self] = "ncs"
    /\ l' = [l EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED << level, last_to_enter >>

e1(self) ==
    /\ pc[self] = "e1"
    /\ IF l[self] < N - 1
          THEN /\ level' = [level EXCEPT ![self] = l[self]]
               /\ pc' = [pc EXCEPT ![self] = "e2"]
          ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
               /\ UNCHANGED level
    /\ UNCHANGED << last_to_enter, l >>

e2(self) ==
    /\ pc[self] = "e2"
    /\ last_to_enter' = [last_to_enter EXCEPT ![l[self]] = self]
    /\ pc' = [pc EXCEPT ![self] = "e3"]
    /\ UNCHANGED << level, l >>

e3(self) ==
    /\ pc[self] = "e3"
    /\ \/ last_to_enter[l[self]] # self
       \/ \A k \in Procs \ {self} : level[k] < l[self]
    /\ l' = [l EXCEPT ![self] = l[self] + 1]
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED << level, last_to_enter >>

cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit_cs"]
    /\ UNCHANGED << level, last_to_enter, l >>

exit_cs(self) ==
    /\ pc[self] = "exit_cs"
    /\ level' = [level EXCEPT ![self] = -1]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED << last_to_enter, l >>

proc(self) ==
    \/ ncs(self)
    \/ e1(self)
    \/ e2(self)
    \/ e3(self)
    \/ cs(self)
    \/ exit_cs(self)

Next == \E self \in Procs : proc(self)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

=============================================================================