---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, TLAPS

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

(*
--algorithm FastMutex
variables x = 0, y = 0, b = [i \in 1..N |-> FALSE];

fair process Proc1 = 1
variables failed1 = FALSE;
begin
ncs1: while TRUE do
        skip;
start1: b[1] := TRUE;
s11:    x := 1;
s21:    if y /= 0 then
s31:      b[1] := FALSE;
s41:      await y = 0;
          goto start1;
        end if;
s51:    y := 1;
s61:    if x /= 1 then
s71:      b[1] := FALSE;
s81:      await \A j \in 2..N : ~b[j];
s91:      if y /= 1 then
s101:       await y = 0;
            goto start1;
          end if;
        end if;
cs1:    skip;
exit1:  y := 0;
e11:    b[1] := FALSE;
      end while;
end process;

fair process ProcSet \in 2..N
variables failed = FALSE;
begin
ncs: while TRUE do
       skip;
start: b[self] := TRUE;
s1:    x := self;
s2:    if y /= 0 then
s3:      b[self] := FALSE;
s4:      await y = 0;
         goto start;
       end if;
s5:    y := self;
s6:    if x /= self then
s7:      b[self] := FALSE;
s8:      await \A j \in (1..N) \ {self} : ~b[j];
s9:      if y /= self then
s10:       await y = 0;
           goto start;
         end if;
       end if;
cs:    skip;
exit:  y := 0;
e1:    b[self] := FALSE;
     end while;
end process;

end algorithm
*)

\* BEGIN TRANSLATION
VARIABLES x, y, b, pc, failed1, failed

vars == << x, y, b, pc, failed1, failed >>

ProcSet == {1} \cup (2..N)

Init == (* Global variables *)
        /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        (* Process Proc1 *)
        /\ failed1 = FALSE
        (* Process ProcSet *)
        /\ failed = [self \in 2..N |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "ncs1"
                                        [] self \in 2..N -> "ncs"]

ncs1 == /\ pc[1] = "ncs1"
        /\ TRUE
        /\ pc' = [pc EXCEPT ![1] = "start1"]
        /\ UNCHANGED << x, y, b, failed1, failed >>

start1 == /\ pc[1] = "start1"
          /\ b' = [b EXCEPT ![1] = TRUE]
          /\ pc' = [pc EXCEPT ![1] = "s11"]
          /\ UNCHANGED << x, y, failed1, failed >>

s11 == /\ pc[1] = "s11"
       /\ x' = 1
       /\ pc' = [pc EXCEPT ![1] = "s21"]
       /\ UNCHANGED << y, b, failed1, failed >>

s21 == /\ pc[1] = "s21"
       /\ IF y /= 0
             THEN /\ pc' = [pc EXCEPT ![1] = "s31"]
             ELSE /\ pc' = [pc EXCEPT ![1] = "s51"]
       /\ UNCHANGED << x, y, b, failed1, failed >>

s31 == /\ pc[1] = "s31"
       /\ b' = [b EXCEPT ![1] = FALSE]
       /\ pc' = [pc EXCEPT ![1] = "s41"]
       /\ UNCHANGED << x, y, failed1, failed >>

s41 == /\ pc[1] = "s41"
       /\ y = 0
       /\ pc' = [pc EXCEPT ![1] = "start1"]
       /\ UNCHANGED << x, y, b, failed1, failed >>

s51 == /\ pc[1] = "s51"
       /\ y' = 1
       /\ pc' = [pc EXCEPT ![1] = "s61"]
       /\ UNCHANGED << x, b, failed1, failed >>

s61 == /\ pc[1] = "s61"
       /\ IF x /= 1
             THEN /\ pc' = [pc EXCEPT ![1] = "s71"]
             ELSE /\ pc' = [pc EXCEPT ![1] = "cs1"]
       /\ UNCHANGED << x, y, b, failed1, failed >>

s71 == /\ pc[1] = "s71"
       /\ b' = [b EXCEPT ![1] = FALSE]
       /\ pc' = [pc EXCEPT ![1] = "s81"]
       /\ UNCHANGED << x, y, failed1, failed >>

s81 == /\ pc[1] = "s81"
       /\ \A j \in 2..N : ~b[j]
       /\ pc' = [pc EXCEPT ![1] = "s91"]
       /\ UNCHANGED << x, y, b, failed1, failed >>

s91 == /\ pc[1] = "s91"
       /\ IF y /= 1
             THEN /\ pc' = [pc EXCEPT ![1] = "s101"]
             ELSE /\ pc' = [pc EXCEPT ![1] = "cs1"]
       /\ UNCHANGED << x, y, b, failed1, failed >>

s101 == /\ pc[1] = "s101"
        /\ y = 0
        /\ pc' = [pc EXCEPT ![1] = "start1"]
        /\ UNCHANGED << x, y, b, failed1, failed >>

cs1 == /\ pc[1] = "cs1"
       /\ TRUE
       /\ pc' = [pc EXCEPT ![1] = "exit1"]
       /\ UNCHANGED << x, y, b, failed1, failed >>

exit1 == /\ pc[1] = "exit1"
         /\ y' = 0
         /\ pc' = [pc EXCEPT ![1] = "e11"]
         /\ UNCHANGED << x, b, failed1, failed >>

e11 == /\ pc[1] = "e11"
       /\ b' = [b EXCEPT ![1] = FALSE]
       /\ pc' = [pc EXCEPT ![1] = "ncs1"]
       /\ UNCHANGED << x, y, failed1, failed >>

Proc1 == ncs1 \/ start1 \/ s11 \/ s21 \/ s31 \/ s41 \/ s51 \/ s61 \/ s71
            \/ s81 \/ s91 \/ s101 \/ cs1 \/ exit1 \/ e11

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, failed1, failed >>

start(self) == /\ pc[self] = "start"
               /\ b' = [b EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "s1"]
               /\ UNCHANGED << x, y, failed1, failed >>

s1(self) == /\ pc[self] = "s1"
            /\ x' = self
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ UNCHANGED << y, b, failed1, failed >>

s2(self) == /\ pc[self] = "s2"
            /\ IF y /= 0
                  THEN /\ pc' = [pc EXCEPT ![self] = "s3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "s5"]
            /\ UNCHANGED << x, y, b, failed1, failed >>

s3(self) == /\ pc[self] = "s3"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "s4"]
            /\ UNCHANGED << x, y, failed1, failed >>

s4(self) == /\ pc[self] = "s4"
            /\ y = 0
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << x, y, b, failed1, failed >>

s5(self) == /\ pc[self] = "s5"
            /\ y' = self
            /\ pc' = [pc EXCEPT ![self] = "s6"]
            /\ UNCHANGED << x, b, failed1, failed >>

s6(self) == /\ pc[self] = "s6"
            /\ IF x /= self
                  THEN /\ pc' = [pc EXCEPT ![self] = "s7"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, failed1, failed >>

s7(self) == /\ pc[self] = "s7"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "s8"]
            /\ UNCHANGED << x, y, failed1, failed >>

s8(self) == /\ pc[self] = "s8"
            /\ \A j \in (1..N) \ {self} : ~b[j]
            /\ pc' = [pc EXCEPT ![self] = "s9"]
            /\ UNCHANGED << x, y, b, failed1, failed >>

s9(self) == /\ pc[self] = "s9"
            /\ IF y /= self
                  THEN /\ pc' = [pc EXCEPT ![self] = "s10"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, failed1, failed >>

s10(self) == /\ pc[self] = "s10"
             /\ y = 0
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, failed1, failed >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << x, y, b, failed1, failed >>

exit(self) == /\ pc[self] = "exit"
              /\ y' = 0
              /\ pc' = [pc EXCEPT ![self] = "e1"]
              /\ UNCHANGED << x, b, failed1, failed >>

e1(self) == /\ pc[self] = "e1"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "ncs"]
            /\ UNCHANGED << x, y, failed1, failed >>

ProcSetProc(self) == ncs(self) \/ start(self) \/ s1(self) \/ s2(self)
                        \/ s3(self) \/ s4(self) \/ s5(self) \/ s6(self)
                        \/ s7(self) \/ s8(self) \/ s9(self) \/ s10(self)
                        \/ cs(self) \/ exit(self) \/ e1(self)

Next == Proc1
           \/ (\E self \in 2..N: ProcSetProc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Proc1)
        /\ \A self \in 2..N : WF_vars(ProcSetProc(self))

\* END TRANSLATION

-----------------------------------------------------------------------------
(* Safety Invariant: Mutual Exclusion *)
(* No two distinct processes are simultaneously in the critical section *)

InCS(p) == IF p = 1 THEN pc[1] = "cs1" ELSE pc[p] = "cs"

MutualExclusion == \A i, j \in 1..N : (i /= j) => ~(InCS(i) /\ InCS(j))

TypeOK == /\ x \in 0..N
          /\ y \in 0..N
          /\ b \in [1..N -> BOOLEAN]
          /\ pc[1] \in {"ncs1", "start1", "s11", "s21", "s31", "s41", 
                        "s51", "s61", "s71", "s81", "s91", "s101", 
                        "cs1", "exit1", "e11"}
          /\ \A p \in 2..N : pc[p] \in {"ncs", "start", "s1", "s2", "s3", 
                                         "s4", "s5", "s6", "s7", "s8", 
                                         "s9", "s10", "cs", "exit", "e1"}

-----------------------------------------------------------------------------
(* Liveness Property *)
(* Infinitely often some process is in the critical section *)

SomeoneInCS == \E p \in 1..N : InCS(p)

Liveness == []<>SomeoneInCS

=============================================================================