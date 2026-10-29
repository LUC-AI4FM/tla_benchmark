---------------------------- MODULE FastMutex ----------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 2

(* --algorithm FastMutex
variables x = 0, y = 0, b = [i \in 1..N |-> FALSE];

process (Proc1 = 1)
variables j1 = 1, failed1 = FALSE;
begin
a_start: while TRUE do
          b[1] := TRUE;
a1:       x := 1;
a2:       if y # 0 then
             b[1] := FALSE;
a3:          await y = 0;
             goto a_start;
          end if;
a4:       y := 1;
a5:       if x # 1 then
             b[1] := FALSE; failed1 := TRUE; j1 := 1;
a6:          while j1 <= N do
                await ~b[j1];
                j1 := j1 + 1;
             end while;
a7:          if y # 1 then
a8:             await y = 0;
                goto a_start;
             end if;
          end if;
a_cs:     failed1 := FALSE;
a9:       y := 0;
a10:      b[1] := FALSE;
         end while;
end process;

process (ProcN \in 2..N)
variables j = 1, failed = FALSE;
begin
p_start: while TRUE do
          b[self] := TRUE;
p1:       x := self;
p2:       if y # 0 then
             b[self] := FALSE;
p3:          await y = 0;
             goto p_start;
          end if;
p4:       y := self;
p5:       if x # self then
             b[self] := FALSE; failed := TRUE; j := 1;
p6:          while j <= N do
                await ~b[j];
                j := j + 1;
             end while;
p7:          if y # self then
p8:             await y = 0;
                goto p_start;
             end if;
          end if;
p_cs:     failed := FALSE;
p9:       y := 0;
p10:      b[self] := FALSE;
         end while;
end process;
end algorithm *)

\* BEGIN TRANSLATION (hand-written, process-uniform)
VARIABLES x, y, b, j, failed, pc

vars == << x, y, b, j, failed, pc >>

ProcSet == {1} \cup (2..N)

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ j = [i \in ProcSet |-> 1]
        /\ failed = [i \in ProcSet |-> FALSE]
        /\ pc = [i \in ProcSet |-> "start"]

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
                       /\ pc' = [pc EXCEPT ![self] = "l3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l4"]
                       /\ b' = b
            /\ UNCHANGED << x, y, j, failed >>

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
                       /\ failed' = [failed EXCEPT ![self] = TRUE]
                       /\ j' = [j EXCEPT ![self] = 1]
                       /\ pc' = [pc EXCEPT ![self] = "l6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ UNCHANGED << b, failed, j >>
            /\ UNCHANGED << x, y >>

l6(self) == /\ pc[self] = "l6"
            /\ IF j[self] <= N
                  THEN /\ ~b[j[self]]
                       /\ j' = [j EXCEPT ![self] = j[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "l6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l7"]
                       /\ j' = j
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
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, j, failed >>

Step(self) == start(self) \/ l1(self) \/ l2(self) \/ l3(self) \/ l4(self)
              \/ l5(self) \/ l6(self) \/ l7(self) \/ l8(self)
              \/ cs(self) \/ l9(self) \/ l10(self)

Proc1 == Step(1)

ProcN(self) == Step(self)

Next == Proc1 \/ (\E self \in 2..N : ProcN(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Proc1)
        /\ \A self \in 2..N : WF_vars(ProcN(self))

\* END TRANSLATION

Invariant == \A i, k \in ProcSet : (i # k) => ~(pc[i] = "cs" /\ pc[k] = "cs")

Liveness == []<>(\E i \in ProcSet : pc[i] = "cs")

=============================================================================