------------------------------ MODULE FastMutex2 ------------------------------
EXTENDS Naturals

CONSTANTS N, M

ASSUME /\ N \in Nat
       /\ M \in Nat
       /\ M <= N

VARIABLES x, y, b, pc, j

vars == << x, y, b, pc, j >>

ProcSet == (1..M) \cup ((M+1)..N)

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ j = [self \in ProcSet |-> 0]
        /\ pc = [self \in ProcSet |-> "ncs"]

(***************************************************************************)
(* Shared step definitions, used by both process groups                    *)
(***************************************************************************)

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, j >>

start(self) == /\ pc[self] = "start"
               /\ b' = [b EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "l1"]
               /\ UNCHANGED << x, y, j >>

l1(self) == /\ pc[self] = "l1"
            /\ x' = self
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << y, b, j >>

l2(self) == /\ pc[self] = "l2"
            /\ IF y # 0
                  THEN pc' = [pc EXCEPT ![self] = "l3"]
                  ELSE pc' = [pc EXCEPT ![self] = "l5"]
            /\ UNCHANGED << x, y, b, j >>

l3(self) == /\ pc[self] = "l3"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "l4"]
            /\ UNCHANGED << x, y, j >>

l4(self) == /\ pc[self] = "l4"
            /\ y = 0
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << x, y, b, j >>

l5(self) == /\ pc[self] = "l5"
            /\ y' = self
            /\ pc' = [pc EXCEPT ![self] = "l6"]
            /\ UNCHANGED << x, b, j >>

l6(self) == /\ pc[self] = "l6"
            /\ IF x # self
                  THEN pc' = [pc EXCEPT ![self] = "l7"]
                  ELSE pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, j >>

l7(self) == /\ pc[self] = "l7"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ j' = [j EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "l8"]
            /\ UNCHANGED << x, y >>

l8(self) == /\ pc[self] = "l8"
            /\ IF j[self] <= N
                  THEN /\ ~b[j[self]]
                       /\ j' = [j EXCEPT ![self] = j[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "l8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l9"]
                       /\ UNCHANGED j
            /\ UNCHANGED << x, y, b >>

l9(self) == /\ pc[self] = "l9"
            /\ IF y # self
                  THEN pc' = [pc EXCEPT ![self] = "l10"]
                  ELSE pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, j >>

l10(self) == /\ pc[self] = "l10"
             /\ y = 0
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, j >>

cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "l11"]
            /\ UNCHANGED << x, y, b, j >>

l11(self) == /\ pc[self] = "l11"
             /\ y' = 0
             /\ pc' = [pc EXCEPT ![self] = "l12"]
             /\ UNCHANGED << x, b, j >>

l12(self) == /\ pc[self] = "l12"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "ncs"]
             /\ UNCHANGED << x, y, j >>

Step(self) == \/ ncs(self) \/ start(self) \/ l1(self) \/ l2(self)
              \/ l3(self) \/ l4(self) \/ l5(self) \/ l6(self)
              \/ l7(self) \/ l8(self) \/ l9(self) \/ l10(self)
              \/ cs(self) \/ l11(self) \/ l12(self)

(***************************************************************************)
(* Two syntactically distinct process types                                *)
(***************************************************************************)

Proc1(self) == Step(self)

Proc2(self) == Step(self)

Next == \/ (\E self \in 1..M : Proc1(self))
        \/ (\E self \in (M+1)..N : Proc2(self))

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in 1..M : WF_vars(Proc1(self))
        /\ \A self \in (M+1)..N : WF_vars(Proc2(self))

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

TypeOK == /\ x \in 0..N
          /\ y \in 0..N
          /\ b \in [1..N -> BOOLEAN]
          /\ j \in [ProcSet -> 0..(N+1)]

Invariant == \A p, q \in ProcSet :
                (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

Liveness == (\E p \in ProcSet : pc[p] \notin {"ncs", "cs", "l11", "l12"})
               ~> (\E p \in ProcSet : pc[p] = "cs")

=============================================================================