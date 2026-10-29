--------------------------- MODULE PetersonN ---------------------------
(***************************************************************************)
(* N-process Peterson mutual exclusion algorithm (filter lock).           *)
(*                                                                         *)
(* --algorithm PetersonN {                                                 *)
(*   variables level = [p \in ProcSet |-> 0],                              *)
(*             last_to_enter = [i \in 1..(N-1) |-> 1];                     *)
(*   process (proc \in ProcSet)                                            *)
(*     variable l = 0;                                                     *)
(*   {                                                                     *)
(*   p1: while (TRUE) {                                                    *)
(*         \* noncritical section                                          *)
(*         l := 1;                                                         *)
(*   p2:   while (l < N) {                                                 *)
(*   p3:     level[self] := l;                                             *)
(*   p4:     last_to_enter[l] := self;                                     *)
(*   p5:     await (\A k \in ProcSet \ {self} : level[k] < l)              *)
(*                 \/ last_to_enter[l] # self;                             *)
(*           l := l + 1;                                                   *)
(*         };                                                              *)
(*   cs:   skip;  \* critical section                                      *)
(*   p6:   level[self] := 0;                                               *)
(*       }                                                                 *)
(*   }                                                                     *)
(* }                                                                       *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N > 1

ProcSet == 1..N

VARIABLES level, last_to_enter, pc, l

vars == << level, last_to_enter, pc, l >>

Init == /\ level = [p \in ProcSet |-> 0]
        /\ last_to_enter = [i \in 1..(N-1) |-> 1]
        /\ l = [self \in ProcSet |-> 0]
        /\ pc = [self \in ProcSet |-> "p1"]

p1(self) == /\ pc[self] = "p1"
            /\ l' = [l EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ UNCHANGED << level, last_to_enter >>

p2(self) == /\ pc[self] = "p2"
            /\ IF l[self] < N
                  THEN pc' = [pc EXCEPT ![self] = "p3"]
                  ELSE pc' = [pc EXCEPT ![self] = "cs"]
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
            /\ \/ \A k \in ProcSet \ {self} : level[k] < l[self]
               \/ last_to_enter[l[self]] # self
            /\ l' = [l EXCEPT ![self] = l[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ UNCHANGED << level, last_to_enter >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "p6"]
            /\ UNCHANGED << level, last_to_enter, l >>

p6(self) == /\ pc[self] = "p6"
            /\ level' = [level EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED << last_to_enter, l >>

proc(self) == p1(self) \/ p2(self) \/ p3(self) \/ p4(self)
                \/ p5(self) \/ cs(self) \/ p6(self)

Next == \E self \in ProcSet : proc(self)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Helper definitions (not part of Spec) *)

TypeOK == /\ level \in [ProcSet -> 0..(N-1)]
          /\ last_to_enter \in [1..(N-1) -> ProcSet]
          /\ l \in [ProcSet -> 0..N]
          /\ pc \in [ProcSet -> {"p1", "p2", "p3", "p4", "p5", "cs", "p6"}]

MutualExclusion == \A i, j \in ProcSet :
                      (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")
=============================================================================