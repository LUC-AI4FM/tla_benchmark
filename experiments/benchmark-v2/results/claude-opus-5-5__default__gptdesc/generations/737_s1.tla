---------------------------- MODULE MCBoulanger ----------------------------
(***************************************************************************)
(* Wrapper around the Boulanger algorithm (Lamport's variant of the        *)
(* bakery algorithm). It adds a bound MaxNat, a finite replacement         *)
(* NatOverride for Nat, and a state constraint that bounds every           *)
(* process's ticket number num[p] below MaxNat.                            *)
(*                                                                         *)
(* The underlying Boulanger specification is included here so that this   *)
(* module parses on its own.                                               *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Procs, MaxNat

ASSUME Procs \subseteq Nat
ASSUME MaxNat \in Nat

(***************************************************************************)
(* Wrapper definitions                                                     *)
(***************************************************************************)
NatOverride == 0 .. MaxNat

(***************************************************************************)
(* The Boulanger algorithm                                                 *)
(***************************************************************************)
a \prec b == \/ a[1] < b[1]
             \/ (a[1] = b[1]) /\ (a[2] < b[2])

VARIABLES num, flag, pc, unchecked, max, nxt, previous

vars == << num, flag, pc, unchecked, max, nxt, previous >>

StateConstraint == \A process \in Procs : num[process] < MaxNat

Labels == {"ncs", "e1", "e2", "e3", "e4", "wait1", "wait2", "cs", "exit"}

TypeOK ==
  /\ num \in [Procs -> Nat]
  /\ flag \in [Procs -> BOOLEAN]
  /\ pc \in [Procs -> Labels]
  /\ unchecked \in [Procs -> SUBSET Procs]
  /\ max \in [Procs -> Nat]
  /\ nxt \in [Procs -> Procs \cup {0}]
  /\ previous \in [Procs -> Nat \cup {-1}]

Init ==
  /\ num = [i \in Procs |-> 0]
  /\ flag = [i \in Procs |-> FALSE]
  /\ unchecked = [i \in Procs |-> {}]
  /\ max = [i \in Procs |-> 0]
  /\ nxt = [i \in Procs |-> 0]
  /\ previous = [i \in Procs |-> -1]
  /\ pc = [i \in Procs |-> "ncs"]

ncs(self) ==
  /\ pc[self] = "ncs"
  /\ pc' = [pc EXCEPT ![self] = "e1"]
  /\ UNCHANGED << num, flag, unchecked, max, nxt, previous >>

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

e2(self) ==
  /\ pc[self] = "e2"
  /\ IF unchecked[self] # {}
       THEN /\ \E i \in unchecked[self] :
                 /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                 /\ IF num[i] > max[self]
                      THEN max' = [max EXCEPT ![self] = num[i]]
                      ELSE UNCHANGED max
            /\ pc' = [pc EXCEPT ![self] = "e2"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "e3"]
            /\ UNCHANGED << unchecked, max >>
  /\ UNCHANGED << num, flag, nxt, previous >>

e3(self) ==
  /\ pc[self] = "e3"
  /\ \/ /\ \E k \in Nat : num' = [num EXCEPT ![self] = k]
        /\ pc' = [pc EXCEPT ![self] = "e3"]
     \/ /\ \E i \in {j \in Nat : j > max[self]} :
              num' = [num EXCEPT ![self] = i]
        /\ pc' = [pc EXCEPT ![self] = "e4"]
  /\ UNCHANGED << flag, unchecked, max, nxt, previous >>

e4(self) ==
  /\ pc[self] = "e4"
  /\ \/ /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
        /\ pc' = [pc EXCEPT ![self] = "e4"]
        /\ UNCHANGED unchecked
     \/ /\ flag' = [flag EXCEPT ![self] = FALSE]
        /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
        /\ pc' = [pc EXCEPT ![self] = "wait1"]
  /\ UNCHANGED << num, max, nxt, previous >>

wait1(self) ==
  /\ pc[self] = "wait1"
  /\ IF unchecked[self] # {}
       THEN /\ \E i \in unchecked[self] :
                 /\ nxt' = [nxt EXCEPT ![self] = i]
                 /\ ~ flag[i]
            /\ previous' = [previous EXCEPT ![self] = -1]
            /\ pc' = [pc EXCEPT ![self] = "wait2"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << nxt, previous >>
  /\ UNCHANGED << num, flag, unchecked, max >>

wait2(self) ==
  /\ pc[self] = "wait2"
  /\ IF \/ num[nxt[self]] = 0
        \/ << num[self], self >> \prec << num[nxt[self]], nxt[self] >>
        \/ /\ previous[self] # -1
           /\ num[nxt[self]] # previous[self]
       THEN /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {nxt[self]}]
            /\ pc' = [pc EXCEPT ![self] = "wait1"]
            /\ UNCHANGED previous
       ELSE /\ previous' = [previous EXCEPT ![self] = num[nxt[self]]]
            /\ pc' = [pc EXCEPT ![self] = "wait2"]
            /\ UNCHANGED unchecked
  /\ UNCHANGED << num, flag, max, nxt >>

cs(self) ==
  /\ pc[self] = "cs"
  /\ pc' = [pc EXCEPT ![self] = "exit"]
  /\ UNCHANGED << num, flag, unchecked, max, nxt, previous >>

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

\* Process is fair except in the noncritical section (label ncs:-)
Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ p(self))

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
MutualExclusion == \A i, j \in Procs : (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

StarvationFree == \A i \in Procs : (pc[i] = "e1") ~> (pc[i] = "cs")

=============================================================================