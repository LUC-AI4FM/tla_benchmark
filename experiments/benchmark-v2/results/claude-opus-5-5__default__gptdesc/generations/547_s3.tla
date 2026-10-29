------------------------------ MODULE OneBitMutex ------------------------------
(***************************************************************************)
(* One-bit mutual exclusion protocol for N processes.                      *)
(*                                                                         *)
(* --algorithm OneBitMutex {                                               *)
(*   variable flag = [i \in 1..N |-> FALSE];                               *)
(*   process (p \in 1..N)                                                  *)
(*     variable j = 1;                                                     *)
(*   {                                                                     *)
(*   ncs: while (TRUE) {                                                   *)
(*          skip;   \* noncritical section                                 *)
(*   e1:    flag[self] := TRUE; j := 1;                                    *)
(*   e2:    while (j < self) {                                             *)
(*            if (flag[j]) {                                               *)
(*   e3:        flag[self] := FALSE;                                       *)
(*   e4:        await ~flag[j];                                            *)
(*              goto e1                                                    *)
(*            } else { j := j + 1 }                                        *)
(*          };                                                             *)
(*          j := self + 1;                                                 *)
(*   e5:    while (j <= N) {                                               *)
(*   e6:      await ~flag[j];                                              *)
(*            j := j + 1                                                   *)
(*          };                                                             *)
(*   cs:    skip;   \* critical section                                    *)
(*   exit:  flag[self] := FALSE                                            *)
(*        }                                                                *)
(*   }                                                                     *)
(* }                                                                       *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 1

VARIABLES flag, pc, j

vars == << flag, pc, j >>

ProcSet == 1..N

Init == /\ flag = [i \in 1..N |-> FALSE]
        /\ j = [self \in ProcSet |-> 1]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED << flag, j >>

e1(self) == /\ pc[self] = "e1"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ j' = [j EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "e2"]

e2(self) == /\ pc[self] = "e2"
            /\ IF j[self] < self
                  THEN IF flag[j[self]]
                          THEN /\ pc' = [pc EXCEPT ![self] = "e3"]
                               /\ j' = j
                          ELSE /\ j' = [j EXCEPT ![self] = j[self] + 1]
                               /\ pc' = [pc EXCEPT ![self] = "e2"]
                  ELSE /\ j' = [j EXCEPT ![self] = self + 1]
                       /\ pc' = [pc EXCEPT ![self] = "e5"]
            /\ flag' = flag

e3(self) == /\ pc[self] = "e3"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "e4"]
            /\ j' = j

e4(self) == /\ pc[self] = "e4"
            /\ ~flag[j[self]]
            /\ pc' = [pc EXCEPT ![self] = "e1"]
            /\ UNCHANGED << flag, j >>

e5(self) == /\ pc[self] = "e5"
            /\ IF j[self] <= N
                  THEN pc' = [pc EXCEPT ![self] = "e6"]
                  ELSE pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << flag, j >>

e6(self) == /\ pc[self] = "e6"
            /\ ~flag[j[self]]
            /\ j' = [j EXCEPT ![self] = j[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "e5"]
            /\ flag' = flag

cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << flag, j >>

exit(self) == /\ pc[self] = "exit"
              /\ flag' = [flag EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ j' = j

p(self) == ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
           \/ e5(self) \/ e6(self) \/ cs(self) \/ exit(self)

Next == \E self \in ProcSet : p(self)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Fair version: processes may stay forever in the noncritical section,   *)
(* but once they leave it they keep taking steps.                          *)
FairSpec == /\ Spec
            /\ \A self \in ProcSet : WF_vars((pc[self] # "ncs") /\ p(self))

-----------------------------------------------------------------------------
TypeOK == /\ flag \in [1..N -> BOOLEAN]
          /\ j \in [ProcSet -> 1..(N+1)]
          /\ pc \in [ProcSet -> {"ncs", "e1", "e2", "e3", "e4",
                                 "e5", "e6", "cs", "exit"}]

MutualExclusion == \A i, k \in ProcSet : (i # k) => ~(pc[i] = "cs" /\ pc[k] = "cs")

Trying(i) == pc[i] \in {"e1", "e2", "e3", "e4", "e5", "e6"}

DeadlockFreedom == (\E i \in ProcSet : Trying(i)) ~> (\E i \in ProcSet : pc[i] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM FairSpec => DeadlockFreedom
=============================================================================