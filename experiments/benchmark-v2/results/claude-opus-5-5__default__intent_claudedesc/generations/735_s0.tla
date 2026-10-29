------------------------------ MODULE Boulangerie ------------------------------
(***************************************************************************)
(* The Boulangerie Algorithm: a variant of Lamport's Bakery Algorithm      *)
(* that works with safe registers. A read that overlaps a write to a safe  *)
(* register may return any value in the register's domain. We model this  *)
(* by letting each write go through any number of arbitrary intermediate  *)
(* values before the intended final value is written. Readers can then    *)
(* observe any of these arbitrary values.                                  *)
(*                                                                         *)
(* Each process examines the other processes one at a time. A process      *)
(* that draws ticket number 1 only needs to check lower-numbered           *)
(* processes.                                                              *)
(***************************************************************************)
EXTENDS Integers

CONSTANT N

ASSUME N \in Nat

Procs == 1..N

(***************************************************************************)
(* Lexicographic ordering on <<ticket number, process id>> pairs.          *)
(***************************************************************************)
a \prec b == \/ a[1] < b[1]
             \/ (a[1] = b[1]) /\ (a[2] < b[2])

VARIABLES num, flag, pc, unchecked, max, nxt, previous

vars == << num, flag, pc, unchecked, max, nxt, previous >>

PCs == {"ncs", "e1", "e2", "e3", "e4", "wait1", "wait2", "cs", "exit"}

TypeOK ==
  /\ num \in [Procs -> Nat]
  /\ flag \in [Procs -> BOOLEAN]
  /\ pc \in [Procs -> PCs]
  /\ unchecked \in [Procs -> SUBSET Procs]
  /\ max \in [Procs -> Nat]
  /\ nxt \in [Procs -> Procs]
  /\ previous \in [Procs -> Nat \cup {-1}]

Init ==
  /\ num = [i \in Procs |-> 0]
  /\ flag = [i \in Procs |-> FALSE]
  /\ unchecked = [self \in Procs |-> {}]
  /\ max = [self \in Procs |-> 0]
  /\ nxt = [self \in Procs |-> 1]
  /\ previous = [self \in Procs |-> -1]
  /\ pc = [self \in Procs |-> "ncs"]

(* Non-critical section: decide to try to enter. *)
ncs(self) ==
  /\ pc[self] = "ncs"
  /\ pc' = [pc EXCEPT ![self] = "e1"]
  /\ UNCHANGED << num, flag, unchecked, max, nxt, previous >>

(* Set flag to TRUE; safe register write may flicker. *)
e1(self) ==
  /\ pc[self] = "e1"
  /\ \/ /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
        /\ pc' = [pc EXCEPT ![self] = "e1"]
        /\ UNCHANGED << unchecked, max >>
     \/ /\ flag' = [flag EXCEPT ![self] = TRUE]
        /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
        /\ max' = [max EXCEPT ![self] = 0]
        /\ pc' = [pc EXCEPT ![self] = "e2"]
  /\ UNCHANGED << num, nxt, previous >>

(* Read the other processes' numbers one at a time, computing the max. *)
e2(self) ==
  /\ pc[self] = "e2"
  /\ IF unchecked[self] # {}
       THEN /\ \E i \in unchecked[self] :
                 /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                 /\ max' = [max EXCEPT ![self] =
                              IF num[i] > max[self] THEN num[i] ELSE max[self]]
            /\ pc' = [pc EXCEPT ![self] = "e2"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "e3"]
            /\ UNCHANGED << unchecked, max >>
  /\ UNCHANGED << num, flag, nxt, previous >>

(* Choose a number larger than max; safe register write. *)
e3(self) ==
  /\ pc[self] = "e3"
  /\ \/ /\ \E k \in Nat : num' = [num EXCEPT ![self] = k]
        /\ pc' = [pc EXCEPT ![self] = "e3"]
     \/ /\ \E i \in {j \in Nat : j > max[self]} :
              num' = [num EXCEPT ![self] = i]
        /\ pc' = [pc EXCEPT ![self] = "e4"]
  /\ UNCHANGED << flag, unchecked, max, nxt, previous >>

(* Reset flag to FALSE; safe register write. Ticket 1 optimization. *)
e4(self) ==
  /\ pc[self] = "e4"
  /\ \/ /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
        /\ pc' = [pc EXCEPT ![self] = "e4"]
        /\ UNCHANGED unchecked
     \/ /\ flag' = [flag EXCEPT ![self] = FALSE]
        /\ unchecked' = [unchecked EXCEPT ![self] =
                           IF num[self] = 1 THEN 1..(self - 1)
                                            ELSE Procs \ {self}]
        /\ pc' = [pc EXCEPT ![self] = "wait1"]
  /\ UNCHANGED << num, max, nxt, previous >>

(* Pick next process to check and wait until its flag is FALSE. *)
wait1(self) ==
  /\ pc[self] = "wait1"
  /\ IF unchecked[self] # {}
       THEN /\ \E i \in unchecked[self] : nxt' = [nxt EXCEPT ![self] = i]
            /\ ~ flag[nxt'[self]]
            /\ previous' = [previous EXCEPT ![self] = -1]
            /\ pc' = [pc EXCEPT ![self] = "wait2"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << nxt, previous >>
  /\ UNCHANGED << num, flag, unchecked, max >>

(* Wait until self has priority over nxt, or nxt's number changed. *)
wait2(self) ==
  /\ pc[self] = "wait2"
  /\ IF \/ num[nxt[self]] = 0
        \/ <<num[self], self>> \prec <<num[nxt[self]], nxt[self]>>
        \/ /\ previous[self] # -1
           /\ num[nxt[self]] # previous[self]
       THEN /\ unchecked' = [unchecked EXCEPT ![self] =
                               unchecked[self] \ {nxt[self]}]
            /\ IF unchecked'[self] = {}
                 THEN pc' = [pc EXCEPT ![self] = "cs"]
                 ELSE pc' = [pc EXCEPT ![self] = "wait1"]
            /\ UNCHANGED previous
       ELSE /\ previous' = [previous EXCEPT ![self] = num[nxt[self]]]
            /\ pc' = [pc EXCEPT ![self] = "wait2"]
            /\ UNCHANGED unchecked
  /\ UNCHANGED << num, flag, max, nxt >>

(* Critical section. *)
cs(self) ==
  /\ pc[self] = "cs"
  /\ pc' = [pc EXCEPT ![self] = "exit"]
  /\ UNCHANGED << num, flag, unchecked, max, nxt, previous >>

(* Exit: reset number to 0; safe register write. *)
exit(self) ==
  /\ pc[self] = "exit"
  /\ \/ /\ \E k \in Nat : num' = [num EXCEPT ![self] = k]
        /\ pc' = [pc EXCEPT ![self] = "exit"]
     \/ /\ num' = [num EXCEPT ![self] = 0]
        /\ pc' = [pc EXCEPT ![self] = "ncs"]
  /\ UNCHANGED << flag, unchecked, max, nxt, previous >>

p(self) == ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
           \/ wait1(self) \/ wait2(self) \/ cs(self) \/ exit(self)

Next == \E self \in Procs : p(self)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ p(self))

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties.                                                 *)
(***************************************************************************)
MutualExclusion == \A i, j \in Procs : (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

Trying(i) == pc[i] \in {"e1", "e2", "e3", "e4", "wait1", "wait2"}

DeadlockFree == (\E i \in Procs : Trying(i)) ~> (\E i \in Procs : pc[i] = "cs")

StarvationFree == \A i \in Procs : (pc[i] = "e1") ~> (pc[i] = "cs")

THEOREM Spec => []TypeOK
THEOREM Spec => []MutualExclusion
THEOREM Spec => DeadlockFree
THEOREM Spec => StarvationFree
=============================================================================