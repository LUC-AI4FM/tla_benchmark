------------------------------ MODULE FastMutex ------------------------------
(***************************************************************************)
(* Lamport's Fast Mutual Exclusion algorithm.  There are two classes of    *)
(* processes: the distinguished process 1 and the processes in 2..N.  Both *)
(* classes run the same protocol over the shared variables x, y, and b.    *)
(* Each process also has a control state pc, a set unchecked used when     *)
(* scanning the b flags, and a failure flag recording that the fast path   *)
(* failed.                                                                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 2

Procs == 1..N

(***************************************************************************
--algorithm FastMutex {
  variables x = 0, y = 0, b = [i \in Procs |-> FALSE];

  fair process (P1 = 1)
    variables unchecked = {}, failed = FALSE;
  {
    ncs:   while (TRUE) {
             skip;
    start:   b[1] := TRUE; failed := FALSE;
    l1:      x := 1;
    l2:      if (y # 0) { b[1] := FALSE; failed := TRUE;
    l2a:                  await y = 0;
                          goto start };
    l3:      y := 1;
    l4:      if (x # 1) { b[1] := FALSE; failed := TRUE;
                          unchecked := Procs \ {1};
    l5:                   while (unchecked # {}) {
                            with (j \in unchecked) { await ~b[j];
                                                     unchecked := unchecked \ {j} } };
    l6:                   if (y # 1) {
    l6a:                    await y = 0;
                            goto start } };
    cs:      skip;
    l7:      y := 0;
    l8:      b[1] := FALSE;
           }
  }

  fair process (Pi \in 2..N)
    variables unchecked = {}, failed = FALSE;
  {
    ncs:   while (TRUE) {
             skip;
    start:   b[self] := TRUE; failed := FALSE;
    l1:      x := self;
    l2:      if (y # 0) { b[self] := FALSE; failed := TRUE;
    l2a:                  await y = 0;
                          goto start };
    l3:      y := self;
    l4:      if (x # self) { b[self] := FALSE; failed := TRUE;
                             unchecked := Procs \ {self};
    l5:                      while (unchecked # {}) {
                               with (j \in unchecked) { await ~b[j];
                                                        unchecked := unchecked \ {j} } };
    l6:                      if (y # self) {
    l6a:                       await y = 0;
                               goto start } };
    cs:      skip;
    l7:      y := 0;
    l8:      b[self] := FALSE;
           }
  }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES x, y, b, pc, unchecked, failed

vars == << x, y, b, pc, unchecked, failed >>

ProcSet == {1} \cup (2..N)

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in Procs |-> FALSE]
        /\ unchecked = [self \in ProcSet |-> {}]
        /\ failed = [self \in ProcSet |-> FALSE]
        /\ pc = [self \in ProcSet |-> "ncs"]

(***************************************************************************)
(* Generic steps, parameterized by the executing process self.            *)
(***************************************************************************)
ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, unchecked, failed >>

start(self) == /\ pc[self] = "start"
               /\ b' = [b EXCEPT ![self] = TRUE]
               /\ failed' = [failed EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "l1"]
               /\ UNCHANGED << x, y, unchecked >>

l1(self) == /\ pc[self] = "l1"
            /\ x' = self
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << y, b, unchecked, failed >>

l2(self) == /\ pc[self] = "l2"
            /\ IF y # 0
                 THEN /\ b' = [b EXCEPT ![self] = FALSE]
                      /\ failed' = [failed EXCEPT ![self] = TRUE]
                      /\ pc' = [pc EXCEPT ![self] = "l2a"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "l3"]
                      /\ UNCHANGED << b, failed >>
            /\ UNCHANGED << x, y, unchecked >>

l2a(self) == /\ pc[self] = "l2a"
             /\ y = 0
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, unchecked, failed >>

l3(self) == /\ pc[self] = "l3"
            /\ y' = self
            /\ pc' = [pc EXCEPT ![self] = "l4"]
            /\ UNCHANGED << x, b, unchecked, failed >>

l4(self) == /\ pc[self] = "l4"
            /\ IF x # self
                 THEN /\ b' = [b EXCEPT ![self] = FALSE]
                      /\ failed' = [failed EXCEPT ![self] = TRUE]
                      /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
                      /\ pc' = [pc EXCEPT ![self] = "l5"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                      /\ UNCHANGED << b, failed, unchecked >>
            /\ UNCHANGED << x, y >>

l5(self) == /\ pc[self] = "l5"
            /\ IF unchecked[self] # {}
                 THEN /\ \E j \in unchecked[self] :
                           /\ ~b[j]
                           /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {j}]
                      /\ pc' = [pc EXCEPT ![self] = "l5"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "l6"]
                      /\ UNCHANGED unchecked
            /\ UNCHANGED << x, y, b, failed >>

l6(self) == /\ pc[self] = "l6"
            /\ IF y # self
                 THEN pc' = [pc EXCEPT ![self] = "l6a"]
                 ELSE pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, unchecked, failed >>

l6a(self) == /\ pc[self] = "l6a"
             /\ y = 0
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, unchecked, failed >>

cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "l7"]
            /\ UNCHANGED << x, y, b, unchecked, failed >>

l7(self) == /\ pc[self] = "l7"
            /\ y' = 0
            /\ pc' = [pc EXCEPT ![self] = "l8"]
            /\ UNCHANGED << x, b, unchecked, failed >>

l8(self) == /\ pc[self] = "l8"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "ncs"]
            /\ UNCHANGED << x, y, unchecked, failed >>

Step(self) == \/ ncs(self) \/ start(self) \/ l1(self) \/ l2(self)
              \/ l2a(self) \/ l3(self) \/ l4(self) \/ l5(self)
              \/ l6(self) \/ l6a(self) \/ cs(self) \/ l7(self) \/ l8(self)

(***************************************************************************)
(* The two process classes.                                               *)
(***************************************************************************)
P1 == Step(1)

Pi(self) == Step(self)

Next == \/ P1
        \/ (\E self \in 2..N : Pi(self))

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(P1)
        /\ \A self \in 2..N : WF_vars(Pi(self))
\* END TRANSLATION

-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties.                                                             *)
(***************************************************************************)
TypeOK == /\ x \in 0..N
          /\ y \in 0..N
          /\ b \in [Procs -> BOOLEAN]
          /\ unchecked \in [ProcSet -> SUBSET Procs]
          /\ failed \in [ProcSet -> BOOLEAN]
          /\ pc \in [ProcSet -> {"ncs", "start", "l1", "l2", "l2a", "l3",
                                 "l4", "l5", "l6", "l6a", "cs", "l7", "l8"}]

MutualExclusion ==
    \A i, j \in ProcSet : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Liveness == []<>(\E i \in ProcSet : pc[i] = "cs")

THEOREM Spec => []MutualExclusion
THEOREM Spec => Liveness
=============================================================================