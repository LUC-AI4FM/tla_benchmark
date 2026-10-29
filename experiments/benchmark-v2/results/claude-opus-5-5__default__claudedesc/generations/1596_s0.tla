------------------------------ MODULE FastMutex2 ------------------------------
EXTENDS Naturals, TLC

CONSTANTS N, M, defaultInitValue

ASSUME /\ N \in Nat
       /\ M \in Nat
       /\ M <= N

VARIABLES x, y, b, pc, j, failed, j2, failed2

vars == << x, y, b, pc, j, failed, j2, failed2 >>

ProcSet == (1..M) \cup ((M+1)..N)

Init == /\ x = defaultInitValue
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        (* Process Proc1 *)
        /\ j = [self \in 1..M |-> defaultInitValue]
        /\ failed = [self \in 1..M |-> FALSE]
        (* Process Proc2 *)
        /\ j2 = [self \in (M+1)..N |-> defaultInitValue]
        /\ failed2 = [self \in (M+1)..N |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self \in 1..M -> "start"
                                        [] self \in (M+1)..N -> "start2"]

(***************************************************************************)
(* Process Proc1                                                           *)
(***************************************************************************)

start(self) == /\ pc[self] = "start"
               /\ pc' = [pc EXCEPT ![self] = "l1"]
               /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l1(self) == /\ pc[self] = "l1"
            /\ b' = [b EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

l2(self) == /\ pc[self] = "l2"
            /\ x' = self
            /\ pc' = [pc EXCEPT ![self] = "l3"]
            /\ UNCHANGED << y, b, j, failed, j2, failed2 >>

l3(self) == /\ pc[self] = "l3"
            /\ IF y # 0
                  THEN pc' = [pc EXCEPT ![self] = "l4"]
                  ELSE pc' = [pc EXCEPT ![self] = "l6"]
            /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l4(self) == /\ pc[self] = "l4"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "l5"]
            /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

l5(self) == /\ pc[self] = "l5"
            /\ y = 0
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l6(self) == /\ pc[self] = "l6"
            /\ y' = self
            /\ pc' = [pc EXCEPT ![self] = "l7"]
            /\ UNCHANGED << x, b, j, failed, j2, failed2 >>

l7(self) == /\ pc[self] = "l7"
            /\ IF x # self
                  THEN pc' = [pc EXCEPT ![self] = "l8"]
                  ELSE pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l8(self) == /\ pc[self] = "l8"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ j' = [j EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "l9"]
            /\ UNCHANGED << x, y, failed, j2, failed2 >>

l9(self) == /\ pc[self] = "l9"
            /\ IF j[self] <= N
                  THEN /\ ~ b[j[self]]
                       /\ j' = [j EXCEPT ![self] = j[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "l9"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l10"]
                       /\ j' = j
            /\ UNCHANGED << x, y, b, failed, j2, failed2 >>

l10(self) == /\ pc[self] = "l10"
             /\ IF y # self
                   THEN pc' = [pc EXCEPT ![self] = "l11"]
                   ELSE pc' = [pc EXCEPT ![self] = "cs"]
             /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l11(self) == /\ pc[self] = "l11"
             /\ y = 0
             /\ failed' = [failed EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "cs"]
             /\ UNCHANGED << x, y, b, j, j2, failed2 >>

cs(self) == /\ pc[self] = "cs"
            /\ IF ~ failed[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "l12"]
                       /\ failed' = failed
                  ELSE /\ failed' = [failed EXCEPT ![self] = FALSE]
                       /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << x, y, b, j, j2, failed2 >>

l12(self) == /\ pc[self] = "l12"
             /\ y' = 0
             /\ pc' = [pc EXCEPT ![self] = "l13"]
             /\ UNCHANGED << x, b, j, failed, j2, failed2 >>

l13(self) == /\ pc[self] = "l13"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

Proc1(self) == start(self) \/ l1(self) \/ l2(self) \/ l3(self) \/ l4(self)
                  \/ l5(self) \/ l6(self) \/ l7(self) \/ l8(self) \/ l9(self)
                  \/ l10(self) \/ l11(self) \/ cs(self) \/ l12(self)
                  \/ l13(self)

(***************************************************************************)
(* Process Proc2                                                           *)
(***************************************************************************)

start2(self) == /\ pc[self] = "start2"
                /\ pc' = [pc EXCEPT ![self] = "l21"]
                /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l21(self) == /\ pc[self] = "l21"
             /\ b' = [b EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "l22"]
             /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

l22(self) == /\ pc[self] = "l22"
             /\ x' = self
             /\ pc' = [pc EXCEPT ![self] = "l23"]
             /\ UNCHANGED << y, b, j, failed, j2, failed2 >>

l23(self) == /\ pc[self] = "l23"
             /\ IF y # 0
                   THEN pc' = [pc EXCEPT ![self] = "l24"]
                   ELSE pc' = [pc EXCEPT ![self] = "l26"]
             /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l24(self) == /\ pc[self] = "l24"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "l25"]
             /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

l25(self) == /\ pc[self] = "l25"
             /\ y = 0
             /\ pc' = [pc EXCEPT ![self] = "start2"]
             /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l26(self) == /\ pc[self] = "l26"
             /\ y' = self
             /\ pc' = [pc EXCEPT ![self] = "l27"]
             /\ UNCHANGED << x, b, j, failed, j2, failed2 >>

l27(self) == /\ pc[self] = "l27"
             /\ IF x # self
                   THEN pc' = [pc EXCEPT ![self] = "l28"]
                   ELSE pc' = [pc EXCEPT ![self] = "cs2"]
             /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l28(self) == /\ pc[self] = "l28"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ j2' = [j2 EXCEPT ![self] = 1]
             /\ pc' = [pc EXCEPT ![self] = "l29"]
             /\ UNCHANGED << x, y, j, failed, failed2 >>

l29(self) == /\ pc[self] = "l29"
             /\ IF j2[self] <= N
                   THEN /\ ~ b[j2[self]]
                        /\ j2' = [j2 EXCEPT ![self] = j2[self] + 1]
                        /\ pc' = [pc EXCEPT ![self] = "l29"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "l210"]
                        /\ j2' = j2
             /\ UNCHANGED << x, y, b, j, failed, failed2 >>

l210(self) == /\ pc[self] = "l210"
              /\ IF y # self
                    THEN pc' = [pc EXCEPT ![self] = "l211"]
                    ELSE pc' = [pc EXCEPT ![self] = "cs2"]
              /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l211(self) == /\ pc[self] = "l211"
              /\ y = 0
              /\ failed2' = [failed2 EXCEPT ![self] = TRUE]
              /\ pc' = [pc EXCEPT ![self] = "cs2"]
              /\ UNCHANGED << x, y, b, j, failed, j2 >>

cs2(self) == /\ pc[self] = "cs2"
             /\ IF ~ failed2[self]
                   THEN /\ pc' = [pc EXCEPT ![self] = "l212"]
                        /\ failed2' = failed2
                   ELSE /\ failed2' = [failed2 EXCEPT ![self] = FALSE]
                        /\ pc' = [pc EXCEPT ![self] = "start2"]
             /\ UNCHANGED << x, y, b, j, failed, j2 >>

l212(self) == /\ pc[self] = "l212"
              /\ y' = 0
              /\ pc' = [pc EXCEPT ![self] = "l213"]
              /\ UNCHANGED << x, b, j, failed, j2, failed2 >>

l213(self) == /\ pc[self] = "l213"
              /\ b' = [b EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "start2"]
              /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

Proc2(self) == start2(self) \/ l21(self) \/ l22(self) \/ l23(self)
                  \/ l24(self) \/ l25(self) \/ l26(self) \/ l27(self)
                  \/ l28(self) \/ l29(self) \/ l210(self) \/ l211(self)
                  \/ cs2(self) \/ l212(self) \/ l213(self)

Next == (\E self \in 1..M : Proc1(self))
           \/ (\E self \in (M+1)..N : Proc2(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..M : WF_vars(Proc1(self))
        /\ \A self \in (M+1)..N : WF_vars(Proc2(self))

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

InCS(i) == IF i \in 1..M
              THEN pc[i] = "cs" /\ ~ failed[i]
              ELSE pc[i] = "cs2" /\ ~ failed2[i]

Mutex == \A i, k \in 1..N : (i # k) => ~ (InCS(i) /\ InCS(k))

Liveness == []<>(\E i \in 1..N : InCS(i))

THEOREM Spec => []Mutex
THEOREM Spec => Liveness
=============================================================================