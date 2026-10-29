------------------------------ MODULE FastMutex2 ------------------------------
EXTENDS Naturals, TLC

CONSTANTS N, M

ASSUME /\ N \in Nat
       /\ M \in Nat
       /\ M =< N

VARIABLES x, y, b, pc, j, failed, j2, failed2

vars == << x, y, b, pc, j, failed, j2, failed2 >>

ProcSet == (1..M) \cup ((M+1)..N)

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ j = [self \in 1..M |-> 1]
        /\ failed = [self \in 1..M |-> FALSE]
        /\ j2 = [self \in (M+1)..N |-> 1]
        /\ failed2 = [self \in (M+1)..N |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self \in 1..M -> "ncs"
                                        [] self \in (M+1)..N -> "ncs2"]

(***************************************************************************)
(* Proc1                                                                   *)
(***************************************************************************)

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

start(self) == /\ pc[self] = "start"
               /\ b' = [b EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "l1"]
               /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

l1(self) == /\ pc[self] = "l1"
            /\ x' = self
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << y, b, j, failed, j2, failed2 >>

l2(self) == /\ pc[self] = "l2"
            /\ IF y # 0
                  THEN pc' = [pc EXCEPT ![self] = "l3"]
                  ELSE pc' = [pc EXCEPT ![self] = "l5"]
            /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l3(self) == /\ pc[self] = "l3"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "l4"]
            /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

l4(self) == /\ pc[self] = "l4"
            /\ y = 0
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l5(self) == /\ pc[self] = "l5"
            /\ y' = self
            /\ pc' = [pc EXCEPT ![self] = "l6"]
            /\ UNCHANGED << x, b, j, failed, j2, failed2 >>

l6(self) == /\ pc[self] = "l6"
            /\ IF x # self
                  THEN pc' = [pc EXCEPT ![self] = "l7"]
                  ELSE pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l7(self) == /\ pc[self] = "l7"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ j' = [j EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "l8"]
            /\ UNCHANGED << x, y, failed, j2, failed2 >>

l8(self) == /\ pc[self] = "l8"
            /\ IF j[self] =< N
                  THEN /\ ~ b[j[self]]
                       /\ j' = [j EXCEPT ![self] = j[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "l8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l9"]
                       /\ j' = j
            /\ UNCHANGED << x, y, b, failed, j2, failed2 >>

l9(self) == /\ pc[self] = "l9"
            /\ IF y # self
                  THEN pc' = [pc EXCEPT ![self] = "l10"]
                  ELSE pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l10(self) == /\ pc[self] = "l10"
             /\ y = 0
             /\ failed' = [failed EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "cs"]
             /\ UNCHANGED << x, y, b, j, j2, failed2 >>

cs(self) == /\ pc[self] = "cs"
            /\ IF ~ failed[self]
                  THEN /\ TRUE
                       /\ pc' = [pc EXCEPT ![self] = "l11"]
                       /\ failed' = failed
                  ELSE /\ failed' = [failed EXCEPT ![self] = FALSE]
                       /\ pc' = [pc EXCEPT ![self] = "ncs"]
            /\ UNCHANGED << x, y, b, j, j2, failed2 >>

l11(self) == /\ pc[self] = "l11"
             /\ y' = 0
             /\ pc' = [pc EXCEPT ![self] = "l12"]
             /\ UNCHANGED << x, b, j, failed, j2, failed2 >>

l12(self) == /\ pc[self] = "l12"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "ncs"]
             /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

Proc1(self) == ncs(self) \/ start(self) \/ l1(self) \/ l2(self) \/ l3(self)
                  \/ l4(self) \/ l5(self) \/ l6(self) \/ l7(self) \/ l8(self)
                  \/ l9(self) \/ l10(self) \/ cs(self) \/ l11(self) \/ l12(self)

(***************************************************************************)
(* Proc2                                                                   *)
(***************************************************************************)

ncs2(self) == /\ pc[self] = "ncs2"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![self] = "start2"]
              /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

start2(self) == /\ pc[self] = "start2"
                /\ b' = [b EXCEPT ![self] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "l12_"]
                /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

l12_(self) == /\ pc[self] = "l12_"
              /\ x' = self
              /\ pc' = [pc EXCEPT ![self] = "l22"]
              /\ UNCHANGED << y, b, j, failed, j2, failed2 >>

l22(self) == /\ pc[self] = "l22"
             /\ IF y # 0
                   THEN pc' = [pc EXCEPT ![self] = "l32"]
                   ELSE pc' = [pc EXCEPT ![self] = "l52"]
             /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l32(self) == /\ pc[self] = "l32"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "l42"]
             /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

l42(self) == /\ pc[self] = "l42"
             /\ y = 0
             /\ pc' = [pc EXCEPT ![self] = "start2"]
             /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l52(self) == /\ pc[self] = "l52"
             /\ y' = self
             /\ pc' = [pc EXCEPT ![self] = "l62"]
             /\ UNCHANGED << x, b, j, failed, j2, failed2 >>

l62(self) == /\ pc[self] = "l62"
             /\ IF x # self
                   THEN pc' = [pc EXCEPT ![self] = "l72"]
                   ELSE pc' = [pc EXCEPT ![self] = "cs2"]
             /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l72(self) == /\ pc[self] = "l72"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ j2' = [j2 EXCEPT ![self] = 1]
             /\ pc' = [pc EXCEPT ![self] = "l82"]
             /\ UNCHANGED << x, y, j, failed, failed2 >>

l82(self) == /\ pc[self] = "l82"
             /\ IF j2[self] =< N
                   THEN /\ ~ b[j2[self]]
                        /\ j2' = [j2 EXCEPT ![self] = j2[self] + 1]
                        /\ pc' = [pc EXCEPT ![self] = "l82"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "l92"]
                        /\ j2' = j2
             /\ UNCHANGED << x, y, b, j, failed, failed2 >>

l92(self) == /\ pc[self] = "l92"
             /\ IF y # self
                   THEN pc' = [pc EXCEPT ![self] = "l102"]
                   ELSE pc' = [pc EXCEPT ![self] = "cs2"]
             /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l102(self) == /\ pc[self] = "l102"
              /\ y = 0
              /\ failed2' = [failed2 EXCEPT ![self] = TRUE]
              /\ pc' = [pc EXCEPT ![self] = "cs2"]
              /\ UNCHANGED << x, y, b, j, failed, j2 >>

cs2(self) == /\ pc[self] = "cs2"
             /\ IF ~ failed2[self]
                   THEN /\ TRUE
                        /\ pc' = [pc EXCEPT ![self] = "l112"]
                        /\ failed2' = failed2
                   ELSE /\ failed2' = [failed2 EXCEPT ![self] = FALSE]
                        /\ pc' = [pc EXCEPT ![self] = "ncs2"]
             /\ UNCHANGED << x, y, b, j, failed, j2 >>

l112(self) == /\ pc[self] = "l112"
              /\ y' = 0
              /\ pc' = [pc EXCEPT ![self] = "l122"]
              /\ UNCHANGED << x, b, j, failed, j2, failed2 >>

l122(self) == /\ pc[self] = "l122"
              /\ b' = [b EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "ncs2"]
              /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

Proc2(self) == ncs2(self) \/ start2(self) \/ l12_(self) \/ l22(self)
                  \/ l32(self) \/ l42(self) \/ l52(self) \/ l62(self)
                  \/ l72(self) \/ l82(self) \/ l92(self) \/ l102(self)
                  \/ cs2(self) \/ l112(self) \/ l122(self)

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

Invariant == \A i, k \in 1..N : (i # k) => ~ (InCS(i) /\ InCS(k))

Liveness == []<>(\E i \in 1..N : InCS(i))

=============================================================================