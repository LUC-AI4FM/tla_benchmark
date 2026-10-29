--------------------------- MODULE PetersonN ---------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 0

Procs == 0..(N-1)

(***************************************************************************
--algorithm Peterson {
    variables level = [k \in Procs |-> -1],
              last_to_enter = [k \in 0..(N-2) |-> -1];

    fair process (p \in Procs)
        variable i = 0;
    {
    ncs:   while (TRUE) {
               skip;
    enter:     i := 0;
    l1:        while (i < N-1) {
    l2:            level[self] := i;
                   last_to_enter[i] := self;
    l3:            await (last_to_enter[i] # self)
                         \/ (\A k \in Procs \ {self} : level[k] < i);
                   i := i + 1
               };
    cs:        skip;
    exit:      level[self] := -1
           }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES level, last_to_enter, pc, i

vars == << level, last_to_enter, pc, i >>

ProcSet == Procs

Init == /\ level = [k \in Procs |-> -1]
        /\ last_to_enter = [k \in 0..(N-2) |-> -1]
        /\ i = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "enter"]
             /\ UNCHANGED << level, last_to_enter, i >>

enter(self) == /\ pc[self] = "enter"
               /\ i' = [i EXCEPT ![self] = 0]
               /\ pc' = [pc EXCEPT ![self] = "l1"]
               /\ UNCHANGED << level, last_to_enter >>

l1(self) == /\ pc[self] = "l1"
            /\ IF i[self] < N-1
                  THEN /\ pc' = [pc EXCEPT ![self] = "l2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << level, last_to_enter, i >>

l2(self) == /\ pc[self] = "l2"
            /\ level' = [level EXCEPT ![self] = i[self]]
            /\ last_to_enter' = [last_to_enter EXCEPT ![i[self]] = self]
            /\ pc' = [pc EXCEPT ![self] = "l3"]
            /\ UNCHANGED i

l3(self) == /\ pc[self] = "l3"
            /\ \/ last_to_enter[i[self]] # self
               \/ \A k \in Procs \ {self} : level[k] < i[self]
            /\ i' = [i EXCEPT ![self] = i[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "l1"]
            /\ UNCHANGED << level, last_to_enter >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << level, last_to_enter, i >>

exit(self) == /\ pc[self] = "exit"
              /\ level' = [level EXCEPT ![self] = -1]
              /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ UNCHANGED << last_to_enter, i >>

p(self) == ncs(self) \/ enter(self) \/ l1(self) \/ l2(self)
              \/ l3(self) \/ cs(self) \/ exit(self)

Next == (\E self \in Procs : p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ p(self))

\* END TRANSLATION

-----------------------------------------------------------------------------

TypeOK ==
    /\ level \in [Procs -> -1..(N-2)]
    /\ last_to_enter \in [0..(N-2) -> Procs \cup {-1}]
    /\ i \in [Procs -> 0..(N-1)]
    /\ pc \in [Procs -> {"ncs", "enter", "l1", "l2", "l3", "cs", "exit"}]

MutualExclusion ==
    \A p1, p2 \in Procs : (p1 # p2) => ~(pc[p1] = "cs" /\ pc[p2] = "cs")

StarvationFree ==
    \A q \in Procs : (pc[q] = "enter") ~> (pc[q] = "cs")

DeadlockFree ==
    (\E q \in Procs : pc[q] = "enter") ~> (\E q \in Procs : pc[q] = "cs")

=============================================================================