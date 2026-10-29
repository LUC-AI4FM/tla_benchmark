------------------------------ MODULE PetersonN ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N >= 1

Procs == 0..(N-1)

Levels == 1..(N-1)

VARIABLES pc, level, last, l

vars == <<pc, level, last, l>>

TypeOK ==
    /\ pc \in [Procs -> {"ncs", "enter", "setlast", "wait", "cs", "exit"}]
    /\ level \in [Procs -> 0..(N-1)]
    /\ last \in [Levels -> Procs \cup {N}]
    /\ l \in [Procs -> 0..N]

Init ==
    /\ pc = [p \in Procs |-> "ncs"]
    /\ level = [p \in Procs |-> 0]
    /\ last = [k \in Levels |-> N]
    /\ l = [p \in Procs |-> 0]

ncs(self) ==
    /\ pc[self] = "ncs"
    /\ l' = [l EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "enter"]
    /\ UNCHANGED <<level, last>>

enter(self) ==
    /\ pc[self] = "enter"
    /\ IF l[self] <= N - 1
         THEN /\ level' = [level EXCEPT ![self] = l[self]]
              /\ pc' = [pc EXCEPT ![self] = "setlast"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
              /\ UNCHANGED level
    /\ UNCHANGED <<last, l>>

setlast(self) ==
    /\ pc[self] = "setlast"
    /\ last' = [last EXCEPT ![l[self]] = self]
    /\ pc' = [pc EXCEPT ![self] = "wait"]
    /\ UNCHANGED <<level, l>>

wait(self) ==
    /\ pc[self] = "wait"
    /\ \/ \A k \in Procs \ {self} : level[k] < l[self]
       \/ last[l[self]] # self
    /\ l' = [l EXCEPT ![self] = l[self] + 1]
    /\ pc' = [pc EXCEPT ![self] = "enter"]
    /\ UNCHANGED <<level, last>>

cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED <<level, last, l>>

exit(self) ==
    /\ pc[self] = "exit"
    /\ level' = [level EXCEPT ![self] = 0]
    /\ l' = [l EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED last

proc(self) ==
    \/ ncs(self)
    \/ enter(self)
    \/ setlast(self)
    \/ wait(self)
    \/ cs(self)
    \/ exit(self)

Next == \E self \in Procs : proc(self)

Fairness ==
    \A self \in Procs :
        /\ WF_vars(enter(self))
        /\ WF_vars(setlast(self))
        /\ SF_vars(wait(self))
        /\ WF_vars(cs(self))
        /\ WF_vars(exit(self))

Spec == Init /\ [][Next]_vars /\ Fairness

MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

StarvationFree ==
    \A p \in Procs : (pc[p] = "enter") ~> (pc[p] = "cs")

=============================================================================