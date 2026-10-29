------------------------------ MODULE Peterson ------------------------------
EXTENDS Integers, TLC

CONSTANT N

ASSUME N \in Nat /\ N > 0

Procs == 0..(N-1)

(***************************************************************************
--algorithm Peterson {
  variables level = [p \in Procs |-> -1],
            last_to_enter = [l \in 0..(N-2) |-> 0];

  fair process (proc \in Procs)
    variable lev = 0;
  {
    ncs:   while (TRUE) {
             skip;
    enter:   while (lev < N-1) {
               level[self] := lev;
    e2:        last_to_enter[lev] := self;
    e3:        await (last_to_enter[lev] # self) \/
                     (\A k \in Procs \ {self} : level[k] < lev);
               lev := lev + 1
             };
    cs:      skip;
    exit:    level[self] := -1;
             lev := 0
           }
  }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES level, last_to_enter, pc, lev

vars == << level, last_to_enter, pc, lev >>

ProcSet == Procs

Init == /\ level = [p \in Procs |-> -1]
        /\ last_to_enter = [l \in 0..(N-2) |-> 0]
        /\ lev = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "enter"]
             /\ UNCHANGED << level, last_to_enter, lev >>

enter(self) == /\ pc[self] = "enter"
               /\ IF lev[self] < N-1
                     THEN /\ level' = [level EXCEPT ![self] = lev[self]]
                          /\ pc' = [pc EXCEPT ![self] = "e2"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                          /\ level' = level
               /\ UNCHANGED << last_to_enter, lev >>

e2(self) == /\ pc[self] = "e2"
            /\ last_to_enter' = [last_to_enter EXCEPT ![lev[self]] = self]
            /\ pc' = [pc EXCEPT ![self] = "e3"]
            /\ UNCHANGED << level, lev >>

e3(self) == /\ pc[self] = "e3"
            /\ \/ last_to_enter[lev[self]] # self
               \/ \A k \in Procs \ {self} : level[k] < lev[self]
            /\ lev' = [lev EXCEPT ![self] = lev[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "enter"]
            /\ UNCHANGED << level, last_to_enter >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << level, last_to_enter, lev >>

exit(self) == /\ pc[self] = "exit"
              /\ level' = [level EXCEPT ![self] = -1]
              /\ lev' = [lev EXCEPT ![self] = 0]
              /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ UNCHANGED last_to_enter

proc(self) == ncs(self) \/ enter(self) \/ e2(self) \/ e3(self)
                 \/ cs(self) \/ exit(self)

Next == (\E self \in Procs : proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ proc(self))

\* END TRANSLATION

TypeOK == /\ level \in [Procs -> -1..(N-1)]
          /\ last_to_enter \in [0..(N-2) -> Procs]
          /\ lev \in [Procs -> 0..(N-1)]
          /\ pc \in [Procs -> {"ncs", "enter", "e2", "e3", "cs", "exit"}]

MutualExclusion == \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

StarvationFree == \A p \in Procs : (pc[p] = "enter") ~> (pc[p] = "cs")

=============================================================================