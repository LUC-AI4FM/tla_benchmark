--------------------------- MODULE PetersonNProc ---------------------------
(***************************************************************************)
(* N-process Peterson mutual exclusion algorithm (filter lock).            *)
(*                                                                         *)
(* --algorithm Peterson {                                                  *)
(*   variables level = [p \in Procs |-> -1],                               *)
(*             last_to_enter = [i \in 0..(N-2) |-> 1];                     *)
(*   process (proc \in Procs)                                              *)
(*     variable l = 0;                                                     *)
(*   {                                                                     *)
(*     ncs: while (TRUE) {                                                 *)
(*            skip;  \* noncritical section                                *)
(*            l := 0;                                                      *)
(*     l0:    while (l < N - 1) {                                          *)
(*     l1:      level[self] := l;                                          *)
(*     l2:      last_to_enter[l] := self;                                  *)
(*     l3:      await (last_to_enter[l] # self)                            *)
(*                    \/ (\A k \in Procs \ {self} : level[k] < l);         *)
(*              l := l + 1                                                 *)
(*            };                                                           *)
(*     cs:    skip;  \* critical section                                   *)
(*     exit:  level[self] := -1                                            *)
(*     }                                                                   *)
(*   }                                                                     *)
(* }                                                                       *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N >= 1

Procs == 1..N

\* BEGIN TRANSLATION
VARIABLES level, last_to_enter, pc, l

vars == << level, last_to_enter, pc, l >>

ProcSet == Procs

Init == (* Global variables *)
        /\ level = [p \in Procs |-> -1]
        /\ last_to_enter = [i \in 0..(N-2) |-> 1]
        (* Process proc *)
        /\ l = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ l' = [l EXCEPT ![self] = 0]
             /\ pc' = [pc EXCEPT ![self] = "l0"]
             /\ UNCHANGED << level, last_to_enter >>

l0(self) == /\ pc[self] = "l0"
            /\ IF l[self] < N - 1
                  THEN /\ pc' = [pc EXCEPT ![self] = "l1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << level, last_to_enter, l >>

l1(self) == /\ pc[self] = "l1"
            /\ level' = [level EXCEPT ![self] = l[self]]
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << last_to_enter, l >>

l2(self) == /\ pc[self] = "l2"
            /\ last_to_enter' = [last_to_enter EXCEPT ![l[self]] = self]
            /\ pc' = [pc EXCEPT ![self] = "l3"]
            /\ UNCHANGED << level, l >>

l3(self) == /\ pc[self] = "l3"
            /\ \/ last_to_enter[l[self]] # self
               \/ \A k \in Procs \ {self} : level[k] < l[self]
            /\ l' = [l EXCEPT ![self] = l[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "l0"]
            /\ UNCHANGED << level, last_to_enter >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << level, last_to_enter, l >>

exit(self) == /\ pc[self] = "exit"
              /\ level' = [level EXCEPT ![self] = -1]
              /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ UNCHANGED << last_to_enter, l >>

proc(self) == ncs(self) \/ l0(self) \/ l1(self) \/ l2(self)
                 \/ l3(self) \/ cs(self) \/ exit(self)

Next == (\E self \in Procs : proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

-----------------------------------------------------------------------------
(* Auxiliary definitions (not part of the described specification proper) *)

TypeOK ==
    /\ level \in [Procs -> -1..(N-2)]
    /\ last_to_enter \in [0..(N-2) -> Procs]
    /\ l \in [Procs -> 0..(N-1)]
    /\ pc \in [Procs -> {"ncs", "l0", "l1", "l2", "l3", "cs", "exit"}]

MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

=============================================================================