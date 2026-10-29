------------------------------- MODULE Peterson -------------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat /\ N > 0

Procs == 0..(N-1)

(***************************************************************************
--algorithm Peterson {
    variables level = [i \in Procs |-> -1],
              last_to_enter = [i \in 0..(N-2) |-> 0];

    fair process (p \in Procs)
      variable l = 0;
    {
      ncs:- while (TRUE) {
              \* noncritical section
              l := 0;
      e1:     while (l < N-1) {
                level[self] := l;
      e2:       last_to_enter[l] := self;
      e3:       await (last_to_enter[l] # self)
                       \/ (\A k \in Procs \ {self} : level[k] < l);
                l := l + 1;
              };
      cs:     skip;  \* critical section
      ex:     level[self] := -1;
            }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES level, last_to_enter, pc, l

vars == << level, last_to_enter, pc, l >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ level = [i \in Procs |-> -1]
        /\ last_to_enter = [i \in 0..(N-2) |-> 0]
        (* Process p *)
        /\ l = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ l' = [l EXCEPT ![self] = 0]
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED << level, last_to_enter >>

e1(self) == /\ pc[self] = "e1"
            /\ IF l[self] < N-1
                  THEN /\ level' = [level EXCEPT ![self] = l[self]]
                       /\ pc' = [pc EXCEPT ![self] = "e2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ level' = level
            /\ UNCHANGED << last_to_enter, l >>

e2(self) == /\ pc[self] = "e2"
            /\ last_to_enter' = [last_to_enter EXCEPT ![l[self]] = self]
            /\ pc' = [pc EXCEPT ![self] = "e3"]
            /\ UNCHANGED << level, l >>

e3(self) == /\ pc[self] = "e3"
            /\ \/ last_to_enter[l[self]] # self
               \/ \A k \in Procs \ {self} : level[k] < l[self]
            /\ l' = [l EXCEPT ![self] = l[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "e1"]
            /\ UNCHANGED << level, last_to_enter >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "ex"]
            /\ UNCHANGED << level, last_to_enter, l >>

ex(self) == /\ pc[self] = "ex"
            /\ level' = [level EXCEPT ![self] = -1]
            /\ pc' = [pc EXCEPT ![self] = "ncs"]
            /\ UNCHANGED << last_to_enter, l >>

p(self) == ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ cs(self) \/ ex(self)

Next == (\E self \in Procs : p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] \notin {"ncs"}) /\ p(self))

\* END TRANSLATION

-----------------------------------------------------------------------------

TypeOK ==
    /\ level \in [Procs -> -1..(N-1)]
    /\ last_to_enter \in [0..(N-2) -> Procs]
    /\ l \in [Procs -> 0..(N-1)]
    /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "cs", "ex"}]

MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* Every process that leaves its noncritical section eventually enters its critical section
StarvationFree ==
    \A i \in Procs : (pc[i] = "e1") ~> (pc[i] = "cs")

\* Some process trying to enter eventually enters
DeadlockFree ==
    (\E i \in Procs : pc[i] = "e1") ~> (\E i \in Procs : pc[i] = "cs")

THEOREM Spec => []TypeOK
THEOREM Spec => []MutualExclusion
THEOREM Spec => StarvationFree
=============================================================================