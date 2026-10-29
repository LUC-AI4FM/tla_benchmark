------------------------------ MODULE FastMutex2 ------------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 2

(* --algorithm FastMutex2
   variables x = 0, y = 0, b = [i \in 1..N |-> FALSE];

   process (Proc1 = 1)
   variable j1 = 0;
   begin
   ncs1: while TRUE do
           skip;
   start1: b[1] := TRUE;
   l11:    x := 1;
   l21:    if y # 0 then
   l31:       b[1] := FALSE;
   l41:       await y = 0;
              goto start1
           end if;
   l51:    y := 1;
   l61:    if x # 1 then
   l71:       b[1] := FALSE;
              j1 := 1;
   l81:       while j1 <= N do
                await ~b[j1];
                j1 := j1 + 1
              end while;
   l91:       if y # 1 then
   l101:         await y = 0;
                 goto start1
              end if
           end if;
   cs1:    skip;
   l111:   y := 0;
   l121:   b[1] := FALSE
         end while
   end process

   process (P \in 2..N)
   variable j = 0;
   begin
   ncs:  while TRUE do
           skip;
   start:  b[self] := TRUE;
   l1:     x := self;
   l2:     if y # 0 then
   l3:        b[self] := FALSE;
   l4:        await y = 0;
              goto start
           end if;
   l5:     y := self;
   l6:     if x # self then
   l7:        b[self] := FALSE;
              j := 1;
   l8:        while j <= N do
                await ~b[j];
                j := j + 1
              end while;
   l9:        if y # self then
   l10:          await y = 0;
                 goto start
              end if
           end if;
   cs:     skip;
   l11:    y := 0;
   l12:    b[self] := FALSE
         end while
   end process
   end algorithm
*)

\* BEGIN TRANSLATION
VARIABLES x, y, b, pc, j1, j

vars == << x, y, b, pc, j1, j >>

ProcSet == {1} \cup (2..N)

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ j1 = 0
        /\ j = [self \in 2..N |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "ncs1"
                                       [] self \in 2..N -> "ncs"]

(***************************************************************************)
(* Process Proc1 (identity 1)                                              *)
(***************************************************************************)

ncs1 == /\ pc[1] = "ncs1"
        /\ pc' = [pc EXCEPT ![1] = "start1"]
        /\ UNCHANGED << x, y, b, j1, j >>

start1 == /\ pc[1] = "start1"
          /\ b' = [b EXCEPT ![1] = TRUE]
          /\ pc' = [pc EXCEPT ![1] = "l11"]
          /\ UNCHANGED << x, y, j1, j >>

l11 == /\ pc[1] = "l11"
       /\ x' = 1
       /\ pc' = [pc EXCEPT ![1] = "l21"]
       /\ UNCHANGED << y, b, j1, j >>

l21 == /\ pc[1] = "l21"
       /\ IF y # 0
             THEN pc' = [pc EXCEPT ![1] = "l31"]
             ELSE pc' = [pc EXCEPT ![1] = "l51"]
       /\ UNCHANGED << x, y, b, j1, j >>

l31 == /\ pc[1] = "l31"
       /\ b' = [b EXCEPT ![1] = FALSE]
       /\ pc' = [pc EXCEPT ![1] = "l41"]
       /\ UNCHANGED << x, y, j1, j >>

l41 == /\ pc[1] = "l41"
       /\ y = 0
       /\ pc' = [pc EXCEPT ![1] = "start1"]
       /\ UNCHANGED << x, y, b, j1, j >>

l51 == /\ pc[1] = "l51"
       /\ y' = 1
       /\ pc' = [pc EXCEPT ![1] = "l61"]
       /\ UNCHANGED << x, b, j1, j >>

l61 == /\ pc[1] = "l61"
       /\ IF x # 1
             THEN pc' = [pc EXCEPT ![1] = "l71"]
             ELSE pc' = [pc EXCEPT ![1] = "cs1"]
       /\ UNCHANGED << x, y, b, j1, j >>

l71 == /\ pc[1] = "l71"
       /\ b' = [b EXCEPT ![1] = FALSE]
       /\ j1' = 1
       /\ pc' = [pc EXCEPT ![1] = "l81"]
       /\ UNCHANGED << x, y, j >>

l81 == /\ pc[1] = "l81"
       /\ IF j1 <= N
             THEN /\ ~b[j1]
                  /\ j1' = j1 + 1
                  /\ pc' = [pc EXCEPT ![1] = "l81"]
             ELSE /\ pc' = [pc EXCEPT ![1] = "l91"]
                  /\ j1' = j1
       /\ UNCHANGED << x, y, b, j >>

l91 == /\ pc[1] = "l91"
       /\ IF y # 1
             THEN pc' = [pc EXCEPT ![1] = "l101"]
             ELSE pc' = [pc EXCEPT ![1] = "cs1"]
       /\ UNCHANGED << x, y, b, j1, j >>

l101 == /\ pc[1] = "l101"
        /\ y = 0
        /\ pc' = [pc EXCEPT ![1] = "start1"]
        /\ UNCHANGED << x, y, b, j1, j >>

cs1 == /\ pc[1] = "cs1"
       /\ pc' = [pc EXCEPT ![1] = "l111"]
       /\ UNCHANGED << x, y, b, j1, j >>

l111 == /\ pc[1] = "l111"
        /\ y' = 0
        /\ pc' = [pc EXCEPT ![1] = "l121"]
        /\ UNCHANGED << x, b, j1, j >>

l121 == /\ pc[1] = "l121"
        /\ b' = [b EXCEPT ![1] = FALSE]
        /\ pc' = [pc EXCEPT ![1] = "ncs1"]
        /\ UNCHANGED << x, y, j1, j >>

Proc1 == ncs1 \/ start1 \/ l11 \/ l21 \/ l31 \/ l41 \/ l51 \/ l61
            \/ l71 \/ l81 \/ l91 \/ l101 \/ cs1 \/ l111 \/ l121

(***************************************************************************)
(* Process group P (identities 2..N)                                       *)
(***************************************************************************)

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, j1, j >>

start(self) == /\ pc[self] = "start"
               /\ b' = [b EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "l1"]
               /\ UNCHANGED << x, y, j1, j >>

l1(self) == /\ pc[self] = "l1"
            /\ x' = self
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << y, b, j1, j >>

l2(self) == /\ pc[self] = "l2"
            /\ IF y # 0
                  THEN pc' = [pc EXCEPT ![self] = "l3"]
                  ELSE pc' = [pc EXCEPT ![self] = "l5"]
            /\ UNCHANGED << x, y, b, j1, j >>

l3(self) == /\ pc[self] = "l3"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "l4"]
            /\ UNCHANGED << x, y, j1, j >>

l4(self) == /\ pc[self] = "l4"
            /\ y = 0
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << x, y, b, j1, j >>

l5(self) == /\ pc[self] = "l5"
            /\ y' = self
            /\ pc' = [pc EXCEPT ![self] = "l6"]
            /\ UNCHANGED << x, b, j1, j >>

l6(self) == /\ pc[self] = "l6"
            /\ IF x # self
                  THEN pc' = [pc EXCEPT ![self] = "l7"]
                  ELSE pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, j1, j >>

l7(self) == /\ pc[self] = "l7"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ j' = [j EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "l8"]
            /\ UNCHANGED << x, y, j1 >>

l8(self) == /\ pc[self] = "l8"
            /\ IF j[self] <= N
                  THEN /\ ~b[j[self]]
                       /\ j' = [j EXCEPT ![self] = j[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "l8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l9"]
                       /\ j' = j
            /\ UNCHANGED << x, y, b, j1 >>

l9(self) == /\ pc[self] = "l9"
            /\ IF y # self
                  THEN pc' = [pc EXCEPT ![self] = "l10"]
                  ELSE pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, j1, j >>

l10(self) == /\ pc[self] = "l10"
             /\ y = 0
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, j1, j >>

cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "l11"]
            /\ UNCHANGED << x, y, b, j1, j >>

l11p(self) == /\ pc[self] = "l11"
              /\ y' = 0
              /\ pc' = [pc EXCEPT ![self] = "l12"]
              /\ UNCHANGED << x, b, j1, j >>

l12(self) == /\ pc[self] = "l12"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "ncs"]
             /\ UNCHANGED << x, y, j1, j >>

P(self) == ncs(self) \/ start(self) \/ l1(self) \/ l2(self) \/ l3(self)
              \/ l4(self) \/ l5(self) \/ l6(self) \/ l7(self) \/ l8(self)
              \/ l9(self) \/ l10(self) \/ cs(self) \/ l11p(self) \/ l12(self)

Next == Proc1
           \/ (\E self \in 2..N : P(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Proc1)
        /\ \A self \in 2..N : WF_vars(P(self))

\* END TRANSLATION

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

TypeOK == /\ x \in 0..N
          /\ y \in 0..N
          /\ b \in [1..N -> BOOLEAN]
          /\ j1 \in 0..(N+1)
          /\ j \in [2..N -> 0..(N+1)]

InCS(i) == IF i = 1 THEN pc[1] = "cs1" ELSE pc[i] = "cs"

Mutex == \A i, k \in 1..N : (i # k) => ~(InCS(i) /\ InCS(k))

Liveness == []<>(\E i \in 1..N : InCS(i))

THEOREM Spec => []Mutex
THEOREM Spec => Liveness
=============================================================================