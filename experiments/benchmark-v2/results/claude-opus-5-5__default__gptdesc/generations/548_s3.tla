------------------------------- MODULE Peterson -------------------------------
(***************************************************************************)
(* N-process Peterson mutual exclusion algorithm (filter lock).            *)
(*                                                                         *)
(* --algorithm Peterson {                                                  *)
(*   variables level = [p \in Procs |-> -1],                               *)
(*             last_to_enter = [l \in 0..(N-2) |-> 1];                     *)
(*   process (proc \in Procs)                                              *)
(*     variable lvl = 0;                                                   *)
(*   {                                                                     *)
(*     p0: while (TRUE) {                                                  *)
(*           \* noncritical section                                        *)
(*     p1:   lvl := 0;                                                     *)
(*     p2:   while (lvl < N - 1) {                                         *)
(*             level[self] := lvl;                                         *)
(*             last_to_enter[lvl] := self;                                 *)
(*     p3:     await \/ last_to_enter[lvl] # self                          *)
(*                   \/ \A q \in Procs \ {self} : level[q] < lvl;          *)
(*             lvl := lvl + 1;                                             *)
(*           };                                                            *)
(*     cs:   skip;  \* critical section                                    *)
(*     exit: level[self] := -1;                                            *)
(*         }                                                               *)
(*   }                                                                     *)
(* }                                                                       *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME N \in Nat \ {0}

Procs == 1..N

\* BEGIN TRANSLATION
VARIABLES level, last_to_enter, pc, lvl

vars == << level, last_to_enter, pc, lvl >>

ProcSet == Procs

Init == (* Global variables *)
        /\ level = [p \in Procs |-> -1]
        /\ last_to_enter = [l \in 0..(N-2) |-> 1]
        (* Process proc *)
        /\ lvl = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "p0"]

p0(self) == /\ pc[self] = "p0"
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED << level, last_to_enter, lvl >>

p1(self) == /\ pc[self] = "p1"
            /\ lvl' = [lvl EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ UNCHANGED << level, last_to_enter >>

p2(self) == /\ pc[self] = "p2"
            /\ IF lvl[self] < N - 1
                  THEN /\ level' = [level EXCEPT ![self] = lvl[self]]
                       /\ last_to_enter' = [last_to_enter EXCEPT ![lvl[self]] = self]
                       /\ pc' = [pc EXCEPT ![self] = "p3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ UNCHANGED << level, last_to_enter >>
            /\ lvl' = lvl

p3(self) == /\ pc[self] = "p3"
            /\ \/ last_to_enter[lvl[self]] # self
               \/ \A q \in Procs \ {self} : level[q] < lvl[self]
            /\ lvl' = [lvl EXCEPT ![self] = lvl[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ UNCHANGED << level, last_to_enter >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << level, last_to_enter, lvl >>

exit(self) == /\ pc[self] = "exit"
              /\ level' = [level EXCEPT ![self] = -1]
              /\ pc' = [pc EXCEPT ![self] = "p0"]
              /\ UNCHANGED << last_to_enter, lvl >>

proc(self) == p0(self) \/ p1(self) \/ p2(self) \/ p3(self)
                 \/ cs(self) \/ exit(self)

Next == (\E self \in Procs : proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ level \in [Procs -> -1..(N-2)]
    /\ last_to_enter \in [0..(N-2) -> Procs]
    /\ lvl \in [Procs -> 0..(N-1)]
    /\ pc \in [Procs -> {"p0", "p1", "p2", "p3", "cs", "exit"}]

MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

=============================================================================