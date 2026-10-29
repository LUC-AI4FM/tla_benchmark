---------------------------- MODULE PetersonN ----------------------------
EXTENDS Integers, Naturals, FiniteSets, TLC

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 2

Procs == 0..(N-1)

(***************************************************************************
--algorithm PetersonN {
    variables level = [i \in Procs |-> -1],
              last_to_enter = [i \in 0..(N-2) |-> -1];

    process (p \in Procs)
        variables l = 0;
    {
     p1: while (TRUE) {
            \* noncritical section
            l := 0;
     p2:    while (l < N - 1) {
     p3:        level[self] := l;
     p4:        last_to_enter[l] := self;
     p5:        await (last_to_enter[l] # self)
                      \/ (\A k \in Procs \ {self} : level[k] < l);
     p6:        l := l + 1;
            };
     cs:    skip;  \* critical section
     p7:    level[self] := -1;
         }
    }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES level, last_to_enter, pc, l

vars == << level, last_to_enter, pc, l >>

ProcSet == Procs

Init == /\ level = [i \in Procs |-> -1]
        /\ last_to_enter = [i \in 0..(N-2) |-> -1]
        /\ l = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "p1"]

p1(self) == /\ pc[self] = "p1"
            /\ l' = [l EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ UNCHANGED << level, last_to_enter >>

p2(self) == /\ pc[self] = "p2"
            /\ IF l[self] < N - 1
                  THEN /\ pc' = [pc EXCEPT ![self] = "p3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << level, last_to_enter, l >>

p3(self) == /\ pc[self] = "p3"
            /\ level' = [level EXCEPT ![self] = l[self]]
            /\ pc' = [pc EXCEPT ![self] = "p4"]
            /\ UNCHANGED << last_to_enter, l >>

p4(self) == /\ pc[self] = "p4"
            /\ last_to_enter' = [last_to_enter EXCEPT ![l[self]] = self]
            /\ pc' = [pc EXCEPT ![self] = "p5"]
            /\ UNCHANGED << level, l >>

p5(self) == /\ pc[self] = "p5"
            /\ \/ last_to_enter[l[self]] # self
               \/ \A k \in Procs \ {self} : level[k] < l[self]
            /\ pc' = [pc EXCEPT ![self] = "p6"]
            /\ UNCHANGED << level, last_to_enter, l >>

p6(self) == /\ pc[self] = "p6"
            /\ l' = [l EXCEPT ![self] = l[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ UNCHANGED << level, last_to_enter >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "p7"]
            /\ UNCHANGED << level, last_to_enter, l >>

p7(self) == /\ pc[self] = "p7"
            /\ level' = [level EXCEPT ![self] = -1]
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED << last_to_enter, l >>

p(self) == p1(self) \/ p2(self) \/ p3(self) \/ p4(self)
              \/ p5(self) \/ p6(self) \/ cs(self) \/ p7(self)

Next == (\E self \in Procs : p(self))

Spec == Init /\ [][Next]_vars
\* END TRANSLATION

TypeOK == /\ level \in [Procs -> -1..(N-2)]
          /\ last_to_enter \in [0..(N-2) -> Procs \cup {-1}]
          /\ l \in [Procs -> 0..(N-1)]
          /\ pc \in [Procs -> {"p1","p2","p3","p4","p5","p6","cs","p7"}]

MutualExclusion == \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

=============================================================================