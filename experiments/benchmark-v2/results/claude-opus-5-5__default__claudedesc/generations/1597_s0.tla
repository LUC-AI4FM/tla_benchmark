------------------------------- MODULE FastMutex -------------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 2

(* --algorithm FastMutex
variables x = 0, y = 0, b = [i \in 1..N |-> FALSE];

process Proc1 = 1
variables j = 1, failed = FALSE;
begin
start:  while TRUE do
          b[1] := TRUE;
l1:       x := 1;
l2:       if y # 0 then
l3:         b[1] := FALSE;
l4:         await y = 0;
            goto start;
          end if;
l5:       y := 1;
l6:       if x # 1 then
l7:         b[1] := FALSE;
            j := 1;
l8:         while j <= N do
              await ~b[j];
              j := j + 1;
            end while;
l9:         if y # 1 then
l10:          await y = 0;
              failed := TRUE;
            end if;
          end if;
l11:      if failed then
            failed := FALSE;
            goto start;
          end if;
cs:       skip;
l12:      y := 0;
l13:      b[1] := FALSE;
        end while;
end process

process Proc2 \in 2..N
variables j2 = 1, failed2 = FALSE;
begin
start2: while TRUE do
          b[self] := TRUE;
m1:       x := self;
m2:       if y # 0 then
m3:         b[self] := FALSE;
m4:         await y = 0;
            goto start2;
          end if;
m5:       y := self;
m6:       if x # self then
m7:         b[self] := FALSE;
            j2 := 1;
m8:         while j2 <= N do
              await ~b[j2];
              j2 := j2 + 1;
            end while;
m9:         if y # self then
m10:          await y = 0;
              failed2 := TRUE;
            end if;
          end if;
m11:      if failed2 then
            failed2 := FALSE;
            goto start2;
          end if;
cs2:      skip;
m12:      y := 0;
m13:      b[self] := FALSE;
        end while;
end process
end algorithm *)

VARIABLES x, y, b, pc, j, failed, j2, failed2

vars == << x, y, b, pc, j, failed, j2, failed2 >>

ProcSet == {1} \cup (2..N)

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ j = 1
        /\ failed = FALSE
        /\ j2 = [self \in 2..N |-> 1]
        /\ failed2 = [self \in 2..N |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "start"
                                       [] self \in 2..N -> "start2"]

(* ---------------- Process 1 ---------------- *)

start == /\ pc[1] = "start"
         /\ b' = [b EXCEPT ![1] = TRUE]
         /\ pc' = [pc EXCEPT ![1] = "l1"]
         /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

l1 == /\ pc[1] = "l1"
      /\ x' = 1
      /\ pc' = [pc EXCEPT ![1] = "l2"]
      /\ UNCHANGED << y, b, j, failed, j2, failed2 >>

l2 == /\ pc[1] = "l2"
      /\ IF y # 0
            THEN pc' = [pc EXCEPT ![1] = "l3"]
            ELSE pc' = [pc EXCEPT ![1] = "l5"]
      /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l3 == /\ pc[1] = "l3"
      /\ b' = [b EXCEPT ![1] = FALSE]
      /\ pc' = [pc EXCEPT ![1] = "l4"]
      /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

l4 == /\ pc[1] = "l4"
      /\ y = 0
      /\ pc' = [pc EXCEPT ![1] = "start"]
      /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l5 == /\ pc[1] = "l5"
      /\ y' = 1
      /\ pc' = [pc EXCEPT ![1] = "l6"]
      /\ UNCHANGED << x, b, j, failed, j2, failed2 >>

l6 == /\ pc[1] = "l6"
      /\ IF x # 1
            THEN pc' = [pc EXCEPT ![1] = "l7"]
            ELSE pc' = [pc EXCEPT ![1] = "l11"]
      /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l7 == /\ pc[1] = "l7"
      /\ b' = [b EXCEPT ![1] = FALSE]
      /\ j' = 1
      /\ pc' = [pc EXCEPT ![1] = "l8"]
      /\ UNCHANGED << x, y, failed, j2, failed2 >>

l8 == /\ pc[1] = "l8"
      /\ IF j <= N
            THEN /\ ~b[j]
                 /\ j' = j + 1
                 /\ pc' = [pc EXCEPT ![1] = "l8"]
            ELSE /\ pc' = [pc EXCEPT ![1] = "l9"]
                 /\ j' = j
      /\ UNCHANGED << x, y, b, failed, j2, failed2 >>

l9 == /\ pc[1] = "l9"
      /\ IF y # 1
            THEN pc' = [pc EXCEPT ![1] = "l10"]
            ELSE pc' = [pc EXCEPT ![1] = "l11"]
      /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l10 == /\ pc[1] = "l10"
       /\ y = 0
       /\ failed' = TRUE
       /\ pc' = [pc EXCEPT ![1] = "l11"]
       /\ UNCHANGED << x, y, b, j, j2, failed2 >>

l11 == /\ pc[1] = "l11"
       /\ IF failed
             THEN /\ failed' = FALSE
                  /\ pc' = [pc EXCEPT ![1] = "start"]
             ELSE /\ pc' = [pc EXCEPT ![1] = "cs"]
                  /\ failed' = failed
       /\ UNCHANGED << x, y, b, j, j2, failed2 >>

cs == /\ pc[1] = "cs"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![1] = "l12"]
      /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

l12 == /\ pc[1] = "l12"
       /\ y' = 0
       /\ pc' = [pc EXCEPT ![1] = "l13"]
       /\ UNCHANGED << x, b, j, failed, j2, failed2 >>

l13 == /\ pc[1] = "l13"
       /\ b' = [b EXCEPT ![1] = FALSE]
       /\ pc' = [pc EXCEPT ![1] = "start"]
       /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

Proc1 == start \/ l1 \/ l2 \/ l3 \/ l4 \/ l5 \/ l6 \/ l7 \/ l8 \/ l9
         \/ l10 \/ l11 \/ cs \/ l12 \/ l13

(* ---------------- Processes 2..N ---------------- *)

start2(self) == /\ pc[self] = "start2"
                /\ b' = [b EXCEPT ![self] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "m1"]
                /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

m1(self) == /\ pc[self] = "m1"
            /\ x' = self
            /\ pc' = [pc EXCEPT ![self] = "m2"]
            /\ UNCHANGED << y, b, j, failed, j2, failed2 >>

m2(self) == /\ pc[self] = "m2"
            /\ IF y # 0
                  THEN pc' = [pc EXCEPT ![self] = "m3"]
                  ELSE pc' = [pc EXCEPT ![self] = "m5"]
            /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

m3(self) == /\ pc[self] = "m3"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "m4"]
            /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

m4(self) == /\ pc[self] = "m4"
            /\ y = 0
            /\ pc' = [pc EXCEPT ![self] = "start2"]
            /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

m5(self) == /\ pc[self] = "m5"
            /\ y' = self
            /\ pc' = [pc EXCEPT ![self] = "m6"]
            /\ UNCHANGED << x, b, j, failed, j2, failed2 >>

m6(self) == /\ pc[self] = "m6"
            /\ IF x # self
                  THEN pc' = [pc EXCEPT ![self] = "m7"]
                  ELSE pc' = [pc EXCEPT ![self] = "m11"]
            /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

m7(self) == /\ pc[self] = "m7"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ j2' = [j2 EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "m8"]
            /\ UNCHANGED << x, y, j, failed, failed2 >>

m8(self) == /\ pc[self] = "m8"
            /\ IF j2[self] <= N
                  THEN /\ ~b[j2[self]]
                       /\ j2' = [j2 EXCEPT ![self] = j2[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "m8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "m9"]
                       /\ j2' = j2
            /\ UNCHANGED << x, y, b, j, failed, failed2 >>

m9(self) == /\ pc[self] = "m9"
            /\ IF y # self
                  THEN pc' = [pc EXCEPT ![self] = "m10"]
                  ELSE pc' = [pc EXCEPT ![self] = "m11"]
            /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

m10(self) == /\ pc[self] = "m10"
             /\ y = 0
             /\ failed2' = [failed2 EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "m11"]
             /\ UNCHANGED << x, y, b, j, failed, j2 >>

m11(self) == /\ pc[self] = "m11"
             /\ IF failed2[self]
                   THEN /\ failed2' = [failed2 EXCEPT ![self] = FALSE]
                        /\ pc' = [pc EXCEPT ![self] = "start2"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "cs2"]
                        /\ failed2' = failed2
             /\ UNCHANGED << x, y, b, j, failed, j2 >>

cs2(self) == /\ pc[self] = "cs2"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "m12"]
             /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

m12(self) == /\ pc[self] = "m12"
             /\ y' = 0
             /\ pc' = [pc EXCEPT ![self] = "m13"]
             /\ UNCHANGED << x, b, j, failed, j2, failed2 >>

m13(self) == /\ pc[self] = "m13"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "start2"]
             /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

Proc2(self) == start2(self) \/ m1(self) \/ m2(self) \/ m3(self) \/ m4(self)
               \/ m5(self) \/ m6(self) \/ m7(self) \/ m8(self) \/ m9(self)
               \/ m10(self) \/ m11(self) \/ cs2(self) \/ m12(self) \/ m13(self)

Next == Proc1 \/ (\E self \in 2..N : Proc2(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Proc1)
        /\ \A self \in 2..N : WF_vars(Proc2(self))

-----------------------------------------------------------------------------

InCS(p) == pc[p] \in {"cs", "cs2"}

TypeOK == /\ x \in 0..N
          /\ y \in 0..N
          /\ b \in [1..N -> BOOLEAN]
          /\ j \in 1..(N+1)
          /\ failed \in BOOLEAN
          /\ j2 \in [2..N -> 1..(N+1)]
          /\ failed2 \in [2..N -> BOOLEAN]

Invariant == \A p, q \in ProcSet : (p # q) => ~(InCS(p) /\ InCS(q))

Liveness == []<>(\E p \in ProcSet : InCS(p))

=============================================================================