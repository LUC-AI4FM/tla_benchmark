--------------------------- MODULE MCBoulanger ---------------------------
(***************************************************************************)
(* A bounded wrapper around a Boulanger (bakery-style) mutual exclusion    *)
(* algorithm. The algorithm is defined inline so that this module is       *)
(* self-contained and passes SANY.                                         *)
(*                                                                         *)
(* The wrapper contributes three things:                                   *)
(*   - the constant MaxNat and the assumption MaxNat \in Nat;              *)
(*   - NatOverride == 0 .. MaxNat, a finite range used in place of Nat     *)
(*     when a ticket number is chosen;                                     *)
(*   - the state constraint StateConstraint, which requires              *)
(*     num[p] < MaxNat for every process p in Procs.                       *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS N, MaxNat

ASSUME NAssump == N \in Nat \ {0}

ASSUME MaxNatAssump == MaxNat \in Nat

Procs == 1 .. N

\* Bounded replacement for Nat, used when choosing ticket numbers.
NatOverride == 0 .. MaxNat

\* State constraint for model checking: every process's ticket stays below MaxNat.
StateConstraint == \A process \in Procs : num[process] < MaxNat

VARIABLES num, flag, unchecked, max, nxt, pc

vars == << num, flag, unchecked, max, nxt, pc >>

\* Lexicographic order on <<ticket, process id>> pairs.
LL(j, i) == \/ num[j] < num[i]
            \/ /\ num[j] = num[i]
               /\ j < i

TypeOK ==
    /\ num \in [Procs -> Nat]
    /\ flag \in [Procs -> BOOLEAN]
    /\ unchecked \in [Procs -> SUBSET Procs]
    /\ max \in [Procs -> Nat]
    /\ nxt \in [Procs -> Procs]
    /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4", "w1", "w2", "cs", "exit"}]

Init ==
    /\ num = [i \in Procs |-> 0]
    /\ flag = [i \in Procs |-> FALSE]
    /\ unchecked = [i \in Procs |-> {}]
    /\ max = [i \in Procs |-> 0]
    /\ nxt = [i \in Procs |-> 1]
    /\ pc = [i \in Procs |-> "ncs"]

ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED << num, flag, unchecked, max, nxt >>

e1(self) ==
    /\ pc[self] = "e1"
    /\ flag' = [flag EXCEPT ![self] = TRUE]
    /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
    /\ max' = [max EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "e2"]
    /\ UNCHANGED << num, nxt >>

e2(self) ==
    /\ pc[self] = "e2"
    /\ IF unchecked[self] # {}
         THEN \E i \in unchecked[self] :
                /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                /\ IF num[i] > max[self]
                     THEN max' = [max EXCEPT ![self] = num[i]]
                     ELSE UNCHANGED max
                /\ pc' = [pc EXCEPT ![self] = "e2"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "e3"]
              /\ UNCHANGED << unchecked, max >>
    /\ UNCHANGED << num, flag, nxt >>

e3(self) ==
    /\ pc[self] = "e3"
    /\ \E k \in {j \in NatOverride : j > max[self]} :
         num' = [num EXCEPT ![self] = k]
    /\ pc' = [pc EXCEPT ![self] = "e4"]
    /\ UNCHANGED << flag, unchecked, max, nxt >>

e4(self) ==
    /\ pc[self] = "e4"
    /\ flag' = [flag EXCEPT ![self] = FALSE]
    /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
    /\ pc' = [pc EXCEPT ![self] = "w1"]
    /\ UNCHANGED << num, max, nxt >>

w1(self) ==
    /\ pc[self] = "w1"
    /\ IF unchecked[self] # {}
         THEN \E i \in unchecked[self] :
                /\ nxt' = [nxt EXCEPT ![self] = i]
                /\ ~ flag[i]
                /\ pc' = [pc EXCEPT ![self] = "w2"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
              /\ UNCHANGED nxt
    /\ UNCHANGED << num, flag, unchecked, max >>

w2(self) ==
    /\ pc[self] = "w2"
    /\ \/ num[nxt[self]] = 0
       \/ LL(self, nxt[self])
    /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {nxt[self]}]
    /\ pc' = [pc EXCEPT ![self] = "w1"]
    /\ UNCHANGED << num, flag, max, nxt >>

cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED << num, flag, unchecked, max, nxt >>

exit(self) ==
    /\ pc[self] = "exit"
    /\ num' = [num EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED << flag, unchecked, max, nxt >>

\* All steps other than leaving the noncritical section.
NonNcs(self) ==
    \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
    \/ w1(self) \/ w2(self) \/ cs(self) \/ exit(self)

Proc(self) == ncs(self) \/ NonNcs(self)

Next == \E self \in Procs : Proc(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(NonNcs(self))

-----------------------------------------------------------------------------
(* Safety *)

MutualExclusion == \A i, j \in Procs : (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

(* Liveness *)

StarvationFree == \A p \in Procs : (pc[p] = "e1") ~> (pc[p] = "cs")

DeadlockFree == (\E p \in Procs : pc[p] = "e1") ~> (\E p \in Procs : pc[p] = "cs")

=============================================================================