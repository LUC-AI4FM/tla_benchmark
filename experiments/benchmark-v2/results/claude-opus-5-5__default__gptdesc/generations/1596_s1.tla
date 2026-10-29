------------------------------ MODULE FastMutex ------------------------------
EXTENDS Naturals, TLC

CONSTANTS M, N

ASSUME /\ N \in Nat \ {0}
       /\ M \in 0..N

(***************************************************************************
--algorithm FastMutex
variables x = 0, y = 0, b = [i \in 1..N |-> FALSE];

process Proc1 \in 1..M
variable j = 0;
begin
ncs:   while TRUE do
         skip;
start:   b[self] := TRUE;
l1:      x := self;
l2:      if y # 0 then
l3:        b[self] := FALSE;
l4:        await y = 0;
           goto start;
         end if;
l5:      y := self;
l6:      if x # self then
l7:        b[self] := FALSE;
           j := 1;
l8:        while j <= N do
             await ~b[j];
             j := j + 1;
           end while;
l9:        if y # self then
l10:         await y = 0;
             goto start;
           end if;
         end if;
cs:      skip;
l11:     y := 0;
l12:     b[self] := FALSE;
       end while;
end process

process Proc2 \in (M+1)..N
variable j2 = 0;
begin
ncs2:  ... (structurally identical copy with labels suffixed "2")
end process
end algorithm
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES x, y, b, pc, j, j2

vars == << x, y, b, pc, j, j2 >>

ProcSet == (1..M) \cup ((M+1)..N)

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ j = [self \in 1..M |-> 0]
        /\ j2 = [self \in (M+1)..N |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in 1..M -> "ncs"
                                        [] self \in (M+1)..N -> "ncs2"]

(***************************************************************************)
(* First process class: 1..M                                               *)
(***************************************************************************)
ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, j, j2 >>

start(self) == /\ pc[self] = "start"
               /\ b' = [b EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "l1"]
               /\ UNCHANGED << x, y, j, j2 >>

l1(self) == /\ pc[self] = "l1"
            /\ x' = self
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << y, b, j, j2 >>

l2(self) == /\ pc[self] = "l2"
            /\ IF y # 0
                  THEN pc' = [pc EXCEPT ![self] = "l3"]
                  ELSE pc' = [pc EXCEPT ![self] = "l5"]
            /\ UNCHANGED << x, y, b, j, j2 >>

l3(self) == /\ pc[self] = "l3"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "l4"]
            /\ UNCHANGED << x, y, j, j2 >>

l4(self) == /\ pc[self] = "l4"
            /\ y = 0
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << x, y, b, j, j2 >>

l5(self) == /\ pc[self] = "l5"
            /\ y' = self
            /\ pc' = [pc EXCEPT ![self] = "l6"]
            /\ UNCHANGED << x, b, j, j2 >>

l6(self) == /\ pc[self] = "l6"
            /\ IF x # self
                  THEN pc' = [pc EXCEPT ![self] = "l7"]
                  ELSE pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, j, j2 >>

l7(self) == /\ pc[self] = "l7"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ j' = [j EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "l8"]
            /\ UNCHANGED << x, y, j2 >>

l8(self) == /\ pc[self] = "l8"
            /\ IF j[self] <= N
                  THEN /\ ~b[j[self]]
                       /\ j' = [j EXCEPT ![self] = j[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "l8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l9"]
                       /\ j' = j
            /\ UNCHANGED << x, y, b, j2 >>

l9(self) == /\ pc[self] = "l9"
            /\ IF y # self
                  THEN pc' = [pc EXCEPT ![self] = "l10"]
                  ELSE pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, j, j2 >>

l10(self) == /\ pc[self] = "l10"
             /\ y = 0
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, j, j2 >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "l11"]
            /\ UNCHANGED << x, y, b, j, j2 >>

l11(self) == /\ pc[self] = "l11"
             /\ y' = 0
             /\ pc' = [pc EXCEPT ![self] = "l12"]
             /\ UNCHANGED << x, b, j, j2 >>

l12(self) == /\ pc[self] = "l12"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "ncs"]
             /\ UNCHANGED << x, y, j, j2 >>

Proc1(self) == ncs(self) \/ start(self) \/ l1(self) \/ l2(self)
                 \/ l3(self) \/ l4(self) \/ l5(self) \/ l6(self)
                 \/ l7(self) \/ l8(self) \/ l9(self) \/ l10(self)
                 \/ cs(self) \/ l11(self) \/ l12(self)

(***************************************************************************)
(* Second process class: (M+1)..N                                          *)
(***************************************************************************)
ncs2(self) == /\ pc[self] = "ncs2"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![self] = "start2"]
              /\ UNCHANGED << x, y, b, j, j2 >>

start2(self) == /\ pc[self] = "start2"
                /\ b' = [b EXCEPT ![self] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "l1_2"]
                /\ UNCHANGED << x, y, j, j2 >>

l1_2(self) == /\ pc[self] = "l1_2"
              /\ x' = self
              /\ pc' = [pc EXCEPT ![self] = "l2_2"]
              /\ UNCHANGED << y, b, j, j2 >>

l2_2(self) == /\ pc[self] = "l2_2"
              /\ IF y # 0
                    THEN pc' = [pc EXCEPT ![self] = "l3_2"]
                    ELSE pc' = [pc EXCEPT ![self] = "l5_2"]
              /\ UNCHANGED << x, y, b, j, j2 >>

l3_2(self) == /\ pc[self] = "l3_2"
              /\ b' = [b EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "l4_2"]
              /\ UNCHANGED << x, y, j, j2 >>

l4_2(self) == /\ pc[self] = "l4_2"
              /\ y = 0
              /\ pc' = [pc EXCEPT ![self] = "start2"]
              /\ UNCHANGED << x, y, b, j, j2 >>

l5_2(self) == /\ pc[self] = "l5_2"
              /\ y' = self
              /\ pc' = [pc EXCEPT ![self] = "l6_2"]
              /\ UNCHANGED << x, b, j, j2 >>

l6_2(self) == /\ pc[self] = "l6_2"
              /\ IF x # self
                    THEN pc' = [pc EXCEPT ![self] = "l7_2"]
                    ELSE pc' = [pc EXCEPT ![self] = "cs2"]
              /\ UNCHANGED << x, y, b, j, j2 >>

l7_2(self) == /\ pc[self] = "l7_2"
              /\ b' = [b EXCEPT ![self] = FALSE]
              /\ j2' = [j2 EXCEPT ![self] = 1]
              /\ pc' = [pc EXCEPT ![self] = "l8_2"]
              /\ UNCHANGED << x, y, j >>

l8_2(self) == /\ pc[self] = "l8_2"
              /\ IF j2[self] <= N
                    THEN /\ ~b[j2[self]]
                         /\ j2' = [j2 EXCEPT ![self] = j2[self] + 1]
                         /\ pc' = [pc EXCEPT ![self] = "l8_2"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "l9_2"]
                         /\ j2' = j2
              /\ UNCHANGED << x, y, b, j >>

l9_2(self) == /\ pc[self] = "l9_2"
              /\ IF y # self
                    THEN pc' = [pc EXCEPT ![self] = "l10_2"]
                    ELSE pc' = [pc EXCEPT ![self] = "cs2"]
              /\ UNCHANGED << x, y, b, j, j2 >>

l10_2(self) == /\ pc[self] = "l10_2"
               /\ y = 0
               /\ pc' = [pc EXCEPT ![self] = "start2"]
               /\ UNCHANGED << x, y, b, j, j2 >>

cs2(self) == /\ pc[self] = "cs2"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "l11_2"]
             /\ UNCHANGED << x, y, b, j, j2 >>

l11_2(self) == /\ pc[self] = "l11_2"
               /\ y' = 0
               /\ pc' = [pc EXCEPT ![self] = "l12_2"]
               /\ UNCHANGED << x, b, j, j2 >>

l12_2(self) == /\ pc[self] = "l12_2"
               /\ b' = [b EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "ncs2"]
               /\ UNCHANGED << x, y, j, j2 >>

Proc2(self) == ncs2(self) \/ start2(self) \/ l1_2(self) \/ l2_2(self)
                 \/ l3_2(self) \/ l4_2(self) \/ l5_2(self) \/ l6_2(self)
                 \/ l7_2(self) \/ l8_2(self) \/ l9_2(self) \/ l10_2(self)
                 \/ cs2(self) \/ l11_2(self) \/ l12_2(self)

Next == \/ (\E self \in 1..M : Proc1(self))
        \/ (\E self \in (M+1)..N : Proc2(self))

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in 1..M : WF_vars(Proc1(self))
        /\ \A self \in (M+1)..N : WF_vars(Proc2(self))
\* END TRANSLATION

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
InCS(i) == pc[i] \in {"cs", "cs2"}

TypeOK == /\ x \in 0..N
          /\ y \in 0..N
          /\ b \in [1..N -> BOOLEAN]

MutualExclusion == \A i, k \in 1..N : (i # k) => ~(InCS(i) /\ InCS(k))

Liveness == []<>(\E i \in 1..N : InCS(i))

THEOREM Spec => []MutualExclusion
=============================================================================