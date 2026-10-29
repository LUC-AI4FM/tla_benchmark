------------------------------ MODULE Session9onebitMC ------------------------------
(***************************************************************************)
(* Model-checking wrapper for the one-bit mutual exclusion algorithm.      *)
(* The original wrapper does EXTENDS Session9onebit. Here the underlying   *)
(* one-bit specification is inlined so that this module is self-contained  *)
(* and passes SANY on its own. The model constants ConstN and ConstProcs   *)
(* fix three processes, and the module states the safety and liveness      *)
(* properties to check over the state variable pc.                         *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS N, Procs

ASSUME /\ N \in Nat \ {0}
       /\ Procs = 0 .. (N - 1)

(***************************************************************************)
(* Model constants: three processes.                                       *)
(***************************************************************************)
ConstN     == 3
ConstProcs == 0 .. (ConstN - 1)

VARIABLES x, unchecked, other, pc

vars == << x, unchecked, other, pc >>

Labels == {"ncs", "e1", "e2", "e3", "e4", "e5", "e6", "cs", "f"}

Trying == {"e1", "e2", "e3", "e4", "e5", "e6"}

TypeOK ==
    /\ x \in [Procs -> BOOLEAN]
    /\ unchecked \in [Procs -> SUBSET Procs]
    /\ other \in [Procs -> Procs]
    /\ pc \in [Procs -> Labels]

Init ==
    /\ x = [i \in Procs |-> FALSE]
    /\ unchecked = [i \in Procs |-> {}]
    /\ other = [i \in Procs |-> 0]
    /\ pc = [i \in Procs |-> "ncs"]

ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED << x, unchecked, other >>

e1(self) ==
    /\ pc[self] = "e1"
    /\ x' = [x EXCEPT ![self] = TRUE]
    /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
    /\ pc' = [pc EXCEPT ![self] = "e2"]
    /\ UNCHANGED other

e2(self) ==
    /\ pc[self] = "e2"
    /\ IF unchecked[self] # {}
          THEN \E i \in unchecked[self] :
                  /\ other' = [other EXCEPT ![self] = i]
                  /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                  /\ pc' = [pc EXCEPT ![self] = "e3"]
          ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
               /\ UNCHANGED << unchecked, other >>
    /\ UNCHANGED x

e3(self) ==
    /\ pc[self] = "e3"
    /\ IF x[other[self]]
          THEN IF self > other[self]
                  THEN pc' = [pc EXCEPT ![self] = "e4"]
                  ELSE pc' = [pc EXCEPT ![self] = "e6"]
          ELSE pc' = [pc EXCEPT ![self] = "e2"]
    /\ UNCHANGED << x, unchecked, other >>

e4(self) ==
    /\ pc[self] = "e4"
    /\ x' = [x EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "e5"]
    /\ UNCHANGED << unchecked, other >>

e5(self) ==
    /\ pc[self] = "e5"
    /\ ~x[other[self]]
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED << x, unchecked, other >>

e6(self) ==
    /\ pc[self] = "e6"
    /\ ~x[other[self]]
    /\ pc' = [pc EXCEPT ![self] = "e2"]
    /\ UNCHANGED << x, unchecked, other >>

cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "f"]
    /\ UNCHANGED << x, unchecked, other >>

f(self) ==
    /\ pc[self] = "f"
    /\ x' = [x EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED << unchecked, other >>

p(self) ==
    \/ ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
    \/ e5(self) \/ e6(self) \/ cs(self) \/ f(self)

Next == \E self \in Procs : p(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

(***************************************************************************)
(* Safety: mutual exclusion.                                               *)
(***************************************************************************)
MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

(***************************************************************************)
(* Deadlock/livelock freedom: if some process is trying to enter, then     *)
(* eventually some process enters the critical section.                    *)
(***************************************************************************)
DeadlockFree ==
    (\E i \in Procs : pc[i] \in Trying) ~> (\E i \in Procs : pc[i] = "cs")

(***************************************************************************)
(* Starvation freedom for process 0.                                       *)
(***************************************************************************)
NoStarveProc0 == (pc[0] \in Trying) ~> (pc[0] = "cs")

(***************************************************************************)
(* Starvation freedom for process 1.                                       *)
(* NOTE: NoStarveProc1 is NOT satisfied by the algorithm.                  *)
(***************************************************************************)
NoStarveProc1 == (pc[1] \in Trying) ~> (pc[1] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => DeadlockFree /\ NoStarveProc0

=============================================================================