------------------------------ MODULE Peterson ------------------------------
(***************************************************************************)
(* Peterson's N-process mutual exclusion algorithm (the "filter lock").    *)
(* Processes in Procs = 0..(N-1) repeatedly cycle through the noncritical  *)
(* section, the entry protocol, the critical section, and the exit.        *)
(* They coordinate using the shared arrays level and last_to_enter.        *)
(***************************************************************************)
EXTENDS Integers, TLC

CONSTANT N

ASSUME NPositive == N \in Nat \ {0}

Procs == 0..(N-1)

(***************************************************************************
--algorithm Peterson {
   variables level = [p \in Procs |-> -1],
             last_to_enter = [l \in 0..(N-2) |-> 0];

   fair process (proc \in Procs)
     variable i = 0;
   {
     ncs:- while (TRUE) {
             skip;
       e1:   while (i < N-1) {
       e2:     level[self] := i;
       e3:     last_to_enter[i] := self;
       e4:     await (last_to_enter[i] # self)
                       \/ (\A k \in Procs \ {self} : level[k] < i);
               i := i + 1;
             };
       cs:   skip;
       exit: level[self] := -1;
             i := 0;
     }
   }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES level, last_to_enter, pc, i

vars == << level, last_to_enter, pc, i >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ level = [p \in Procs |-> -1]
        /\ last_to_enter = [l \in 0..(N-2) |-> 0]
        (* Process proc *)
        /\ i = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED << level, last_to_enter, i >>

e1(self) == /\ pc[self] = "e1"
            /\ IF i[self] < N-1
                  THEN /\ pc' = [pc EXCEPT ![self] = "e2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << level, last_to_enter, i >>

e2(self) == /\ pc[self] = "e2"
            /\ level' = [level EXCEPT ![self] = i[self]]
            /\ pc' = [pc EXCEPT ![self] = "e3"]
            /\ UNCHANGED << last_to_enter, i >>

e3(self) == /\ pc[self] = "e3"
            /\ last_to_enter' = [last_to_enter EXCEPT ![i[self]] = self]
            /\ pc' = [pc EXCEPT ![self] = "e4"]
            /\ UNCHANGED << level, i >>

e4(self) == /\ pc[self] = "e4"
            /\ \/ last_to_enter[i[self]] # self
               \/ \A k \in Procs \ {self} : level[k] < i[self]
            /\ i' = [i EXCEPT ![self] = i[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "e1"]
            /\ UNCHANGED << level, last_to_enter >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << level, last_to_enter, i >>

exit(self) == /\ pc[self] = "exit"
              /\ level' = [level EXCEPT ![self] = -1]
              /\ i' = [i EXCEPT ![self] = 0]
              /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ UNCHANGED last_to_enter

proc(self) == ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
                 \/ cs(self) \/ exit(self)

Next == (\E self \in Procs : proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ proc(self))

\* END TRANSLATION

-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK ==
    /\ level \in [Procs -> -1..(N-2)]
    /\ last_to_enter \in [0..(N-2) -> Procs]
    /\ i \in [Procs -> 0..(N-1)]
    /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4", "cs", "exit"}]

\* Safety: no two distinct processes are in the critical section at once.
MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

\* Liveness: every process that starts the entry protocol eventually
\* enters its critical section.
StarvationFree ==
    \A p \in Procs : (pc[p] = "e1") ~> (pc[p] = "cs")

\* Liveness: if some process is trying, some process eventually enters cs.
DeadlockFree ==
    (\E p \in Procs : pc[p] = "e1") ~> (\E p \in Procs : pc[p] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => StarvationFree /\ DeadlockFree
=============================================================================