---------------------------- MODULE FastMutex ----------------------------
(***************************************************************************)
(* Lamport's Fast Mutual Exclusion algorithm.                              *)
(* Process 1 is a distinguished process; processes 2..N form a family.     *)
(* Both classes run the same entry/exit protocol on shared variables       *)
(* x, y and b. Each process also has a loop index j and a failure flag     *)
(* that records whether its current entry attempt has failed.              *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 1

Procs == 1..N

VARIABLES x, y, b, j, failed, pc

vars == << x, y, b, j, failed, pc >>

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in Procs |-> FALSE]
        /\ j = [i \in Procs |-> 1]
        /\ failed = [i \in Procs |-> FALSE]
        /\ pc = [i \in Procs |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, j, failed >>

start(self) == /\ pc[self] = "start"
               /\ b' = [b EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "l1"]
               /\ UNCHANGED << x, y, j, failed >>

l1(self) == /\ pc[self] = "l1"
            /\ x' = self
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << y, b, j, failed >>

l2(self) == /\ pc[self] = "l2"
            /\ IF y # 0
                 THEN /\ b' = [b EXCEPT ![self] = FALSE]
                      /\ failed' = [failed EXCEPT ![self] = TRUE]
                      /\ pc' = [pc EXCEPT ![self] = "l3"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "l4"]
                      /\ UNCHANGED << b, failed >>
            /\ UNCHANGED << x, y, j >>

l3(self) == /\ pc[self] = "l3"
            /\ y = 0
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << x, y, b, j, failed >>

l4(self) == /\ pc[self] = "l4"
            /\ y' = self
            /\ pc' = [pc EXCEPT ![self] = "l5"]
            /\ UNCHANGED << x, b, j, failed >>

l5(self) == /\ pc[self] = "l5"
            /\ IF x # self
                 THEN /\ b' = [b EXCEPT ![self] = FALSE]
                      /\ j' = [j EXCEPT ![self] = 1]
                      /\ failed' = [failed EXCEPT ![self] = TRUE]
                      /\ pc' = [pc EXCEPT ![self] = "l6"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                      /\ UNCHANGED << b, j, failed >>
            /\ UNCHANGED << x, y >>

l6(self) == /\ pc[self] = "l6"
            /\ IF j[self] <= N
                 THEN /\ ~b[j[self]]
                      /\ j' = [j EXCEPT ![self] = j[self] + 1]
                      /\ pc' = [pc EXCEPT ![self] = "l6"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "l7"]
                      /\ UNCHANGED j
            /\ UNCHANGED << x, y, b, failed >>

l7(self) == /\ pc[self] = "l7"
            /\ IF y # self
                 THEN pc' = [pc EXCEPT ![self] = "l8"]
                 ELSE pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, j, failed >>

l8(self) == /\ pc[self] = "l8"
            /\ y = 0
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << x, y, b, j, failed >>

cs(self) == /\ pc[self] = "cs"
            /\ failed' = [failed EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "l9"]
            /\ UNCHANGED << x, y, b, j >>

l9(self) == /\ pc[self] = "l9"
            /\ y' = 0
            /\ pc' = [pc EXCEPT ![self] = "l10"]
            /\ UNCHANGED << x, b, j, failed >>

l10(self) == /\ pc[self] = "l10"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "ncs"]
             /\ UNCHANGED << x, y, j, failed >>

Body(self) == \/ ncs(self) \/ start(self) \/ l1(self) \/ l2(self)
              \/ l3(self) \/ l4(self) \/ l5(self) \/ l6(self)
              \/ l7(self) \/ l8(self) \/ cs(self) \/ l9(self)
              \/ l10(self)

(* The distinguished process 1 *)
Proc1 == Body(1)

(* The family of processes 2..N *)
ProcN(self) == Body(self)

Next == \/ Proc1
        \/ (\E self \in 2..N : ProcN(self))

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(Proc1)
        /\ \A self \in 2..N : WF_vars(ProcN(self))

TypeOK == /\ x \in 0..N
          /\ y \in 0..N
          /\ b \in [Procs -> BOOLEAN]
          /\ j \in [Procs -> 1..(N+1)]
          /\ failed \in [Procs -> BOOLEAN]
          /\ pc \in [Procs -> {"ncs", "start", "l1", "l2", "l3", "l4", "l5",
                               "l6", "l7", "l8", "cs", "l9", "l10"}]

MutualExclusion ==
    \A i, k \in Procs : (i # k) => ~(pc[i] = "cs" /\ pc[k] = "cs")

Liveness == []<>(\E i \in Procs : pc[i] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
=============================================================================