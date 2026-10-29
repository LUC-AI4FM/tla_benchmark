------------------------------ MODULE Peterson ------------------------------
(***************************************************************************)
(* Peterson's N-process mutual exclusion algorithm (the "filter" lock).   *)
(* Each process repeatedly cycles through its noncritical section, an     *)
(* entry protocol of N-1 levels, the critical section, and an exit.       *)
(* Shared arrays level and last_to_enter coordinate access.               *)
(***************************************************************************)
EXTENDS Naturals, Integers

CONSTANTS N, Procs

ASSUME /\ N \in Nat
       /\ N > 0
       /\ Procs = 0..(N-1)

(***************************************************************************
--algorithm Peterson {
  variables level = [p \in Procs |-> -1],
            last_to_enter = [l \in 0..(N-2) |-> 0];

  process (proc \in Procs)
    variable i = 0;
  {
    ncs:  while (TRUE) {
            skip;  \* noncritical section
    enter:  i := 0;
    l1:     while (i < N-1) {
              level[self] := i;
    l2:       last_to_enter[i] := self;
    l3:       await (last_to_enter[i] # self)
                      \/ (\A k \in Procs \ {self} : level[k] < i);
              i := i + 1;
            };
    cs:     skip;  \* critical section
    exit:   level[self] := -1;
          }
  }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES level, last_to_enter, pc, i

vars == << level, last_to_enter, pc, i >>

ProcSet == Procs

Init == /\ level = [p \in Procs |-> -1]
        /\ last_to_enter = [l \in 0..(N-2) |-> 0]
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
                  THEN /\ level' = [level EXCEPT ![self] = i[self]]
                       /\ pc' = [pc EXCEPT ![self] = "l2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ level' = level
            /\ UNCHANGED << last_to_enter, i >>

l2(self) == /\ pc[self] = "l2"
            /\ last_to_enter' = [last_to_enter EXCEPT ![i[self]] = self]
            /\ pc' = [pc EXCEPT ![self] = "l3"]
            /\ UNCHANGED << level, i >>

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

proc(self) == ncs(self) \/ enter(self) \/ l1(self) \/ l2(self)
                 \/ l3(self) \/ cs(self) \/ exit(self)

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
    /\ pc \in [Procs -> {"ncs", "enter", "l1", "l2", "l3", "cs", "exit"}]

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

\* Every process that leaves its noncritical section eventually enters
\* its critical section.
StarvationFreedom ==
    \A p \in Procs : (pc[p] = "enter") ~> (pc[p] = "cs")

\* Some process trying to enter eventually succeeds.
DeadlockFreedom ==
    (\E p \in Procs : pc[p] = "enter") ~> (\E p \in Procs : pc[p] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => StarvationFreedom
=============================================================================