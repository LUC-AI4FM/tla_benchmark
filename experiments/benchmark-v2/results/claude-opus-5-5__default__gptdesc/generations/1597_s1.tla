-------------------------- MODULE FastMutex2Classes --------------------------
(***************************************************************************)
(* Lamport's Fast Mutual Exclusion algorithm with two classes of           *)
(* processes: a distinguished process 1 and processes 2..N.  Shared        *)
(* variables x, y and b coordinate entry into the critical section.  Each  *)
(* process has a control state pc, a loop index j and a failure flag       *)
(* failed, which records that the fast path failed.                        *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 2

Procs == 1..N

(***************************************************************************
--algorithm FastMutex2 {
  variables x = 0, y = 0, b = [i \in Procs |-> FALSE];

  fair process (P1 = 1)
    variables j1 = 1, failed1 = FALSE;
  { s1:  while (TRUE) {
           failed1 := FALSE;
           b[1] := TRUE;
     a1:   x := 1;
     a2:   if (y # 0) { b[1] := FALSE; failed1 := TRUE;
     a2w:    await y = 0; goto s1 };
     a3:   y := 1;
     a4:   if (x # 1) { b[1] := FALSE; failed1 := TRUE; j1 := 1;
     a4a:    while (j1 <= N) { await ~b[j1]; j1 := j1 + 1 };
     a4b:    if (y # 1) {
     a4c:      await y = 0; goto s1 } };
     cs1:  skip;
     a5:   y := 0;
     a6:   b[1] := FALSE
         }
  }

  fair process (P2 \in 2..N)
    variables j2 = 1, failed2 = FALSE;
  { s2:  while (TRUE) {
           failed2 := FALSE;
           b[self] := TRUE;
     c1:   x := self;
     c2:   if (y # 0) { b[self] := FALSE; failed2 := TRUE;
     c2w:    await y = 0; goto s2 };
     c3:   y := self;
     c4:   if (x # self) { b[self] := FALSE; failed2 := TRUE; j2 := 1;
     c4a:    while (j2 <= N) { await ~b[j2]; j2 := j2 + 1 };
     c4b:    if (y # self) {
     c4c:      await y = 0; goto s2 } };
     cs2:  skip;
     c5:   y := 0;
     c6:   b[self] := FALSE
         }
  }
}
 ***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES x, y, b, pc, j1, failed1, j2, failed2

vars == << x, y, b, pc, j1, failed1, j2, failed2 >>

ProcSet == {1} \cup (2..N)

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in Procs |-> FALSE]
        /\ j1 = 1
        /\ failed1 = FALSE
        /\ j2 = [self \in 2..N |-> 1]
        /\ failed2 = [self \in 2..N |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "s1"
                                        [] self \in 2..N -> "s2"]

(*************************** Process 1 *************************************)

s1 == /\ pc[1] = "s1"
      /\ failed1' = FALSE
      /\ b' = [b EXCEPT ![1] = TRUE]
      /\ pc' = [pc EXCEPT ![1] = "a1"]
      /\ UNCHANGED << x, y, j1, j2, failed2 >>

a1 == /\ pc[1] = "a1"
      /\ x' = 1
      /\ pc' = [pc EXCEPT ![1] = "a2"]
      /\ UNCHANGED << y, b, j1, failed1, j2, failed2 >>

a2 == /\ pc[1] = "a2"
      /\ IF y # 0
            THEN /\ b' = [b EXCEPT ![1] = FALSE]
                 /\ failed1' = TRUE
                 /\ pc' = [pc EXCEPT ![1] = "a2w"]
            ELSE /\ pc' = [pc EXCEPT ![1] = "a3"]
                 /\ UNCHANGED << b, failed1 >>
      /\ UNCHANGED << x, y, j1, j2, failed2 >>

a2w == /\ pc[1] = "a2w"
       /\ y = 0
       /\ pc' = [pc EXCEPT ![1] = "s1"]
       /\ UNCHANGED << x, y, b, j1, failed1, j2, failed2 >>

a3 == /\ pc[1] = "a3"
      /\ y' = 1
      /\ pc' = [pc EXCEPT ![1] = "a4"]
      /\ UNCHANGED << x, b, j1, failed1, j2, failed2 >>

a4 == /\ pc[1] = "a4"
      /\ IF x # 1
            THEN /\ b' = [b EXCEPT ![1] = FALSE]
                 /\ failed1' = TRUE
                 /\ j1' = 1
                 /\ pc' = [pc EXCEPT ![1] = "a4a"]
            ELSE /\ pc' = [pc EXCEPT ![1] = "cs1"]
                 /\ UNCHANGED << b, failed1, j1 >>
      /\ UNCHANGED << x, y, j2, failed2 >>

a4a == /\ pc[1] = "a4a"
       /\ IF j1 <= N
             THEN /\ ~b[j1]
                  /\ j1' = j1 + 1
                  /\ pc' = [pc EXCEPT ![1] = "a4a"]
             ELSE /\ pc' = [pc EXCEPT ![1] = "a4b"]
                  /\ j1' = j1
       /\ UNCHANGED << x, y, b, failed1, j2, failed2 >>

a4b == /\ pc[1] = "a4b"
       /\ IF y # 1
             THEN pc' = [pc EXCEPT ![1] = "a4c"]
             ELSE pc' = [pc EXCEPT ![1] = "cs1"]
       /\ UNCHANGED << x, y, b, j1, failed1, j2, failed2 >>

a4c == /\ pc[1] = "a4c"
       /\ y = 0
       /\ pc' = [pc EXCEPT ![1] = "s1"]
       /\ UNCHANGED << x, y, b, j1, failed1, j2, failed2 >>

cs1 == /\ pc[1] = "cs1"
       /\ pc' = [pc EXCEPT ![1] = "a5"]
       /\ UNCHANGED << x, y, b, j1, failed1, j2, failed2 >>

a5 == /\ pc[1] = "a5"
      /\ y' = 0
      /\ pc' = [pc EXCEPT ![1] = "a6"]
      /\ UNCHANGED << x, b, j1, failed1, j2, failed2 >>

a6 == /\ pc[1] = "a6"
      /\ b' = [b EXCEPT ![1] = FALSE]
      /\ pc' = [pc EXCEPT ![1] = "s1"]
      /\ UNCHANGED << x, y, j1, failed1, j2, failed2 >>

P1 == s1 \/ a1 \/ a2 \/ a2w \/ a3 \/ a4 \/ a4a \/ a4b \/ a4c
         \/ cs1 \/ a5 \/ a6

(*************************** Processes 2..N ********************************)

s2(self) == /\ pc[self] = "s2"
            /\ failed2' = [failed2 EXCEPT ![self] = FALSE]
            /\ b' = [b EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "c1"]
            /\ UNCHANGED << x, y, j1, failed1, j2 >>

c1(self) == /\ pc[self] = "c1"
            /\ x' = self
            /\ pc' = [pc EXCEPT ![self] = "c2"]
            /\ UNCHANGED << y, b, j1, failed1, j2, failed2 >>

c2(self) == /\ pc[self] = "c2"
            /\ IF y # 0
                  THEN /\ b' = [b EXCEPT ![self] = FALSE]
                       /\ failed2' = [failed2 EXCEPT ![self] = TRUE]
                       /\ pc' = [pc EXCEPT ![self] = "c2w"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "c3"]
                       /\ UNCHANGED << b, failed2 >>
            /\ UNCHANGED << x, y, j1, failed1, j2 >>

c2w(self) == /\ pc[self] = "c2w"
             /\ y = 0
             /\ pc' = [pc EXCEPT ![self] = "s2"]
             /\ UNCHANGED << x, y, b, j1, failed1, j2, failed2 >>

c3(self) == /\ pc[self] = "c3"
            /\ y' = self
            /\ pc' = [pc EXCEPT ![self] = "c4"]
            /\ UNCHANGED << x, b, j1, failed1, j2, failed2 >>

c4(self) == /\ pc[self] = "c4"
            /\ IF x # self
                  THEN /\ b' = [b EXCEPT ![self] = FALSE]
                       /\ failed2' = [failed2 EXCEPT ![self] = TRUE]
                       /\ j2' = [j2 EXCEPT ![self] = 1]
                       /\ pc' = [pc EXCEPT ![self] = "c4a"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs2"]
                       /\ UNCHANGED << b, failed2, j2 >>
            /\ UNCHANGED << x, y, j1, failed1 >>

c4a(self) == /\ pc[self] = "c4a"
             /\ IF j2[self] <= N
                   THEN /\ ~b[j2[self]]
                        /\ j2' = [j2 EXCEPT ![self] = j2[self] + 1]
                        /\ pc' = [pc EXCEPT ![self] = "c4a"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "c4b"]
                        /\ j2' = j2
             /\ UNCHANGED << x, y, b, j1, failed1, failed2 >>

c4b(self) == /\ pc[self] = "c4b"
             /\ IF y # self
                   THEN pc' = [pc EXCEPT ![self] = "c4c"]
                   ELSE pc' = [pc EXCEPT ![self] = "cs2"]
             /\ UNCHANGED << x, y, b, j1, failed1, j2, failed2 >>

c4c(self) == /\ pc[self] = "c4c"
             /\ y = 0
             /\ pc' = [pc EXCEPT ![self] = "s2"]
             /\ UNCHANGED << x, y, b, j1, failed1, j2, failed2 >>

cs2(self) == /\ pc[self] = "cs2"
             /\ pc' = [pc EXCEPT ![self] = "c5"]
             /\ UNCHANGED << x, y, b, j1, failed1, j2, failed2 >>

c5(self) == /\ pc[self] = "c5"
            /\ y' = 0
            /\ pc' = [pc EXCEPT ![self] = "c6"]
            /\ UNCHANGED << x, b, j1, failed1, j2, failed2 >>

c6(self) == /\ pc[self] = "c6"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ UNCHANGED << x, y, j1, failed1, j2, failed2 >>

P2(self) == s2(self) \/ c1(self) \/ c2(self) \/ c2w(self) \/ c3(self)
              \/ c4(self) \/ c4a(self) \/ c4b(self) \/ c4c(self)
              \/ cs2(self) \/ c5(self) \/ c6(self)

Next == P1 \/ (\E self \in 2..N : P2(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(P1)
        /\ \A self \in 2..N : WF_vars(P2(self))
\* END TRANSLATION

-----------------------------------------------------------------------------

InCS(i) == IF i = 1 THEN pc[i] = "cs1" ELSE pc[i] = "cs2"

TypeOK == /\ x \in 0..N
          /\ y \in 0..N
          /\ b \in [Procs -> BOOLEAN]
          /\ j1 \in 1..(N+1)
          /\ failed1 \in BOOLEAN
          /\ j2 \in [2..N -> 1..(N+1)]
          /\ failed2 \in [2..N -> BOOLEAN]

(* Mutual exclusion: no two distinct processes are in the CS together. *)
Mutex == \A i, k \in ProcSet : (i # k) => ~(InCS(i) /\ InCS(k))

(* Liveness: infinitely often some process is in the critical section. *)
Liveness == []<>(\E i \in ProcSet : InCS(i))

THEOREM Spec => [](TypeOK /\ Mutex)
THEOREM Spec => Liveness
=============================================================================