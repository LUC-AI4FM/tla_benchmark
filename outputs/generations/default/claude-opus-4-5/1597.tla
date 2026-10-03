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
start1:
    while TRUE do
        ncs1: skip;
        st1:  b[1] := TRUE;
        st2:  x := 1;
        st3:  if y # 0 then
        st4:      b[1] := FALSE;
        st5:      await y = 0;
              goto st1;
              end if;
        st6:  y := 1;
        st7:  if x # 1 then
        st8:      b[1] := FALSE;
        st9:      await \A j \in 2..N : ~b[j];
        st10:     if y # 1 then
        st11:         await y = 0;
                  goto st1;
                  end if;
              end if;
        cs1:  skip;  \* critical section
        st12: y := 0;
        st13: b[1] := FALSE;
    end while;
end process;

fair process ProcN \in 2..N
variables failedN = FALSE;
begin
startN:
    while TRUE do
        ncsN: skip;
        stN1:  b[self] := TRUE;
        stN2:  x := self;
        stN3:  if y # 0 then
        stN4:      b[self] := FALSE;
        stN5:      await y = 0;
               goto stN1;
               end if;
        stN6:  y := self;
        stN7:  if x # self then
        stN8:      b[self] := FALSE;
        stN9:      await \A j \in 1..N : (j = self) \/ ~b[j];
        stN10:     if y # self then
        stN11:         await y = 0;
                   goto stN1;
                   end if;
               end if;
        csN:  skip;  \* critical section
        stN12: y := 0;
        stN13: b[self] := FALSE;
    end while;
end process;

end algorithm;
*)

\* BEGIN TRANSLATION
VARIABLES x, y, b, pc, failed1, failedN

vars == << x, y, b, pc, failed1, failedN >>

ProcSet == {1} \cup (2..N)

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ failed1 = FALSE
        /\ failedN = [self \in 2..N |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "ncs1"
                                        [] self \in 2..N -> "ncsN"]

ncs1 == /\ pc[1] = "ncs1"
        /\ TRUE
        /\ pc' = [pc EXCEPT ![1] = "st1"]
        /\ UNCHANGED << x, y, b, failed1, failedN >>

st1 == /\ pc[1] = "st1"
       /\ b' = [b EXCEPT ![1] = TRUE]
       /\ pc' = [pc EXCEPT ![1] = "st2"]
       /\ UNCHANGED << x, y, failed1, failedN >>

st2 == /\ pc[1] = "st2"
       /\ x' = 1
       /\ pc' = [pc EXCEPT ![1] = "st3"]
       /\ UNCHANGED << y, b, failed1, failedN >>

st3 == /\ pc[1] = "st3"
       /\ IF y # 0
             THEN /\ pc' = [pc EXCEPT ![1] = "st4"]
             ELSE /\ pc' = [pc EXCEPT ![1] = "st6"]
       /\ UNCHANGED << x, y, b, failed1, failedN >>

st4 == /\ pc[1] = "st4"
       /\ b' = [b EXCEPT ![1] = FALSE]
       /\ pc' = [pc EXCEPT ![1] = "st5"]
       /\ UNCHANGED << x, y, failed1, failedN >>

st5 == /\ pc[1] = "st5"
       /\ y = 0
       /\ pc' = [pc EXCEPT ![1] = "st1"]
       /\ UNCHANGED << x, y, b, failed1, failedN >>

st6 == /\ pc[1] = "st6"
       /\ y' = 1
       /\ pc' = [pc EXCEPT ![1] = "st7"]
       /\ UNCHANGED << x, b, failed1, failedN >>

st7 == /\ pc[1] = "st7"
       /\ IF x # 1
             THEN /\ pc' = [pc EXCEPT ![1] = "st8"]
             ELSE /\ pc' = [pc EXCEPT ![1] = "cs1"]
       /\ UNCHANGED << x, y, b, failed1, failedN >>

st8 == /\ pc[1] = "st8"
       /\ b' = [b EXCEPT ![1] = FALSE]
       /\ pc' = [pc EXCEPT ![1] = "st9"]
       /\ UNCHANGED << x, y, failed1, failedN >>

st9 == /\ pc[1] = "st9"
       /\ \A j \in 2..N : ~b[j]
       /\ pc' = [pc EXCEPT ![1] = "st10"]
       /\ UNCHANGED << x, y, b, failed1, failedN >>

st10 == /\ pc[1] = "st10"
        /\ IF y # 1
              THEN /\ pc' = [pc EXCEPT ![1] = "st11"]
              ELSE /\ pc' = [pc EXCEPT ![1] = "cs1"]
        /\ UNCHANGED << x, y, b, failed1, failedN >>

st11 == /\ pc[1] = "st11"
        /\ y = 0
        /\ pc' = [pc EXCEPT ![1] = "st1"]
        /\ UNCHANGED << x, y, b, failed1, failedN >>

cs1 == /\ pc[1] = "cs1"
       /\ TRUE
       /\ pc' = [pc EXCEPT ![1] = "st12"]
       /\ UNCHANGED << x, y, b, failed1, failedN >>

st12 == /\ pc[1] = "st12"
        /\ y' = 0
        /\ pc' = [pc EXCEPT ![1] = "st13"]
        /\ UNCHANGED << x, b, failed1, failedN >>

st13 == /\ pc[1] = "st13"
        /\ b' = [b EXCEPT ![1] = FALSE]
        /\ pc' = [pc EXCEPT ![1] = "ncs1"]
        /\ UNCHANGED << x, y, failed1, failedN >>

Proc1 == ncs1 \/ st1 \/ st2 \/ st3 \/ st4 \/ st5 \/ st6 \/ st7 \/ st8 
            \/ st9 \/ st10 \/ st11 \/ cs1 \/ st12 \/ st13

ncsN(self) == /\ pc[self] = "ncsN"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![self] = "stN1"]
              /\ UNCHANGED << x, y, b, failed1, failedN >>

stN1(self) == /\ pc[self] = "stN1"
              /\ b' = [b EXCEPT ![self] = TRUE]
              /\ pc' = [pc EXCEPT ![self] = "stN2"]
              /\ UNCHANGED << x, y, failed1, failedN >>

stN2(self) == /\ pc[self] = "stN2"
              /\ x' = self
              /\ pc' = [pc EXCEPT ![self] = "stN3"]
              /\ UNCHANGED << y, b, failed1, failedN >>

stN3(self) == /\ pc[self] = "stN3"
              /\ IF y # 0
                    THEN /\ pc' = [pc EXCEPT ![self] = "stN4"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "stN6"]
              /\ UNCHANGED << x, y, b, failed1, failedN >>

stN4(self) == /\ pc[self] = "stN4"
              /\ b' = [b EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "stN5"]
              /\ UNCHANGED << x, y, failed1, failedN >>

stN5(self) == /\ pc[self] = "stN5"
              /\ y = 0
              /\ pc' = [pc EXCEPT ![self] = "stN1"]
              /\ UNCHANGED << x, y, b, failed1, failedN >>

stN6(self) == /\ pc[self] = "stN6"
              /\ y' = self
              /\ pc' = [pc EXCEPT ![self] = "stN7"]
              /\ UNCHANGED << x, b, failed1, failedN >>

stN7(self) == /\ pc[self] = "stN7"
              /\ IF x # self
                    THEN /\ pc' = [pc EXCEPT ![self] = "stN8"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "csN"]
              /\ UNCHANGED << x, y, b, failed1, failedN >>

stN8(self) == /\ pc[self] = "stN8"
              /\ b' = [b EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "stN9"]
              /\ UNCHANGED << x, y, failed1, failedN >>

stN9(self) == /\ pc[self] = "stN9"
              /\ \A j \in 1..N : (j = self) \/ ~b[j]
              /\ pc' = [pc EXCEPT ![self] = "stN10"]
              /\ UNCHANGED << x, y, b, failed1, failedN >>

stN10(self) == /\ pc[self] = "stN10"
               /\ IF y # self
                     THEN /\ pc' = [pc EXCEPT ![self] = "stN11"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "csN"]
               /\ UNCHANGED << x, y, b, failed1, failedN >>

stN11(self) == /\ pc[self] = "stN11"
               /\ y = 0
               /\ pc' = [pc EXCEPT ![self] = "stN1"]
               /\ UNCHANGED << x, y, b, failed1, failedN >>

csN(self) == /\ pc[self] = "csN"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "stN12"]
             /\ UNCHANGED << x, y, b, failed1, failedN >>

stN12(self) == /\ pc[self] = "stN12"
               /\ y' = 0
               /\ pc' = [pc EXCEPT ![self] = "stN13"]
               /\ UNCHANGED << x, b, failed1, failedN >>

stN13(self) == /\ pc[self] = "stN13"
               /\ b' = [b EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "ncsN"]
               /\ UNCHANGED << x, y, failed1, failedN >>

ProcN(self) == ncsN(self) \/ stN1(self) \/ stN2(self) \/ stN3(self)
                  \/ stN4(self) \/ stN5(self) \/ stN6(self) \/ stN7(self)
                  \/ stN8(self) \/ stN9(self) \/ stN10(self) \/ stN11(self)
                  \/ csN(self) \/ stN12(self) \/ stN13(self)

Next == Proc1
           \/ (\E self \in 2..N: ProcN(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Proc1)
        /\ \A self \in 2..N : WF_vars(ProcN(self))

\* END TRANSLATION

-----------------------------------------------------------------------------

(* Safety: Mutual Exclusion Invariant *)
InCS(i) == IF i = 1 THEN pc[1] = "cs1" ELSE pc[i] = "csN"

MutualExclusion == \A i, j \in 1..N : (i # j) => ~(InCS(i) /\ InCS(j))

TypeOK == /\ x \in 0..N
          /\ y \in 0..N
          /\ b \in [1..N -> BOOLEAN]
          /\ pc \in [ProcSet -> STRING]

(* Liveness: Infinitely often some process is in the critical section *)
SomeoneInCS == \E i \in 1..N : InCS(i)

Liveness == []<>SomeoneInCS

=============================================================================