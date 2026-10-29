------------------------------ MODULE OneBitMutex ------------------------------
(***************************************************************************)
(* The one-bit mutual exclusion algorithm for N processes (Burns/Lamport). *)
(* Each process cycles through noncritical section, entry, critical        *)
(* section and exit.  It uses a shared boolean array flag and a local      *)
(* index j to scan the other processes, backing off when it sees           *)
(* contention from a lower-numbered process and waiting on higher ones.   *)
(*                                                                         *)
(* --algorithm OneBit {                                                    *)
(*   variable flag = [i \in 1..N |-> FALSE];                               *)
(*   process (P \in 1..N)                                                  *)
(*     variable j = 1;                                                     *)
(*   { ncs:   while (TRUE) {                                               *)
(*              skip;                                                      *)
(*     entry:   flag[self] := TRUE;                                        *)
(*              j := 1;                                                    *)
(*     e2:      while (j < self) {                                         *)
(*                if (flag[j]) {                                           *)
(*     e3:          flag[self] := FALSE;                                   *)
(*     e4:          await ~flag[j];                                        *)
(*                  goto entry }                                           *)
(*                else j := j + 1 };                                       *)
(*     e5:      j := self + 1;                                             *)
(*     e6:      while (j <= N) {                                           *)
(*     e7:        await ~flag[j];                                          *)
(*                j := j + 1 };                                            *)
(*     cs:      skip;                                                      *)
(*     exit:    flag[self] := FALSE                                        *)
(*   } } }                                                                 *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

Procs == 1..N

\* BEGIN TRANSLATION
VARIABLES flag, pc, j

vars == << flag, pc, j >>

ProcSet == Procs

Init == /\ flag = [i \in 1..N |-> FALSE]
        /\ j = [self \in Procs |-> 1]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "entry"]
             /\ UNCHANGED << flag, j >>

entry(self) == /\ pc[self] = "entry"
               /\ flag' = [flag EXCEPT ![self] = TRUE]
               /\ j' = [j EXCEPT ![self] = 1]
               /\ pc' = [pc EXCEPT ![self] = "e2"]

e2(self) == /\ pc[self] = "e2"
            /\ IF j[self] < self
                  THEN /\ IF flag[j[self]]
                             THEN /\ pc' = [pc EXCEPT ![self] = "e3"]
                                  /\ j' = j
                             ELSE /\ j' = [j EXCEPT ![self] = j[self] + 1]
                                  /\ pc' = [pc EXCEPT ![self] = "e2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "e5"]
                       /\ j' = j
            /\ flag' = flag

e3(self) == /\ pc[self] = "e3"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "e4"]
            /\ j' = j

e4(self) == /\ pc[self] = "e4"
            /\ ~flag[j[self]]
            /\ pc' = [pc EXCEPT ![self] = "entry"]
            /\ UNCHANGED << flag, j >>

e5(self) == /\ pc[self] = "e5"
            /\ j' = [j EXCEPT ![self] = self + 1]
            /\ pc' = [pc EXCEPT ![self] = "e6"]
            /\ flag' = flag

e6(self) == /\ pc[self] = "e6"
            /\ IF j[self] <= N
                  THEN /\ pc' = [pc EXCEPT ![self] = "e7"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << flag, j >>

e7(self) == /\ pc[self] = "e7"
            /\ ~flag[j[self]]
            /\ j' = [j EXCEPT ![self] = j[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "e6"]
            /\ flag' = flag

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << flag, j >>

exit(self) == /\ pc[self] = "exit"
              /\ flag' = [flag EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ j' = j

P(self) == ncs(self) \/ entry(self) \/ e2(self) \/ e3(self) \/ e4(self)
              \/ e5(self) \/ e6(self) \/ e7(self) \/ cs(self) \/ exit(self)

Next == (\E self \in Procs : P(self))

Spec == Init /\ [][Next]_vars
\* END TRANSLATION

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
TypeOK == /\ flag \in [Procs -> BOOLEAN]
          /\ j \in [Procs -> 1..(N+1)]
          /\ pc \in [Procs -> {"ncs", "entry", "e2", "e3", "e4", "e5",
                               "e6", "e7", "cs", "exit"}]

MutualExclusion == \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
=============================================================================