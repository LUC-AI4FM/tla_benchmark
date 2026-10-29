---------------------------- MODULE MCBoulanger ----------------------------
(***************************************************************************)
(* Model-checking configuration for the Boulanger version of Lamport's     *)
(* bakery algorithm. The infinite set Nat is replaced by the finite set    *)
(* 0..MaxNat, so TLC can explore the whole state space.                    *)
(*                                                                         *)
(* TLC configuration:                                                      *)
(*   CONSTANTS N = 3, MaxNat = 3                                           *)
(*   SPECIFICATION Spec                                                    *)
(*   CONSTRAINT StateConstraint                                            *)
(*   INVARIANTS MutualExclusion TypeOK Inv                                 *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS N, MaxNat

ASSUME /\ N \in Nat \ {0}
       /\ MaxNat \in Nat

\* Bounded replacement for Nat used in model checking.
MCNat == 0..MaxNat

Procs == 1..N

\* Lexicographic order on <<ticket, process id>> pairs.
a \prec b == \/ a[1] < b[1]
             \/ (a[1] = b[1]) /\ (a[2] < b[2])

VARIABLES num, flag, pc, unchecked, max, nxt

vars == << num, flag, pc, unchecked, max, nxt >>

Init == /\ num = [i \in Procs |-> 0]
        /\ flag = [i \in Procs |-> FALSE]
        /\ unchecked = [self \in Procs |-> {}]
        /\ max = [self \in Procs |-> 0]
        /\ nxt = [self \in Procs |-> 1]
        /\ pc = [self \in Procs |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED << num, flag, unchecked, max, nxt >>

e1(self) == /\ pc[self] = "e1"
            /\ \/ /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
                  /\ pc' = [pc EXCEPT ![self] = "e1"]
                  /\ UNCHANGED << unchecked, max >>
               \/ /\ flag' = [flag EXCEPT ![self] = TRUE]
                  /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
                  /\ max' = [max EXCEPT ![self] = 0]
                  /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ UNCHANGED << num, nxt >>

e2(self) == /\ pc[self] = "e2"
            /\ IF unchecked[self] # {}
                  THEN /\ \E i \in unchecked[self] :
                            /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                            /\ max' = [max EXCEPT ![self] =
                                         IF num[i] > max[self] THEN num[i] ELSE max[self]]
                       /\ pc' = [pc EXCEPT ![self] = "e2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "e3"]
                       /\ UNCHANGED << unchecked, max >>
            /\ UNCHANGED << num, flag, nxt >>

e3(self) == /\ pc[self] = "e3"
            /\ \/ /\ \E k \in MCNat : num' = [num EXCEPT ![self] = k]
                  /\ pc' = [pc EXCEPT ![self] = "e3"]
               \/ /\ \E i \in {j \in MCNat : j > max[self]} :
                        num' = [num EXCEPT ![self] = i]
                  /\ pc' = [pc EXCEPT ![self] = "e4"]
            /\ UNCHANGED << flag, unchecked, max, nxt >>

e4(self) == /\ pc[self] = "e4"
            /\ \/ /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
                  /\ pc' = [pc EXCEPT ![self] = "e4"]
                  /\ UNCHANGED unchecked
               \/ /\ flag' = [flag EXCEPT ![self] = FALSE]
                  /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
                  /\ pc' = [pc EXCEPT ![self] = "w1"]
            /\ UNCHANGED << num, max, nxt >>

w1(self) == /\ pc[self] = "w1"
            /\ IF unchecked[self] # {}
                  THEN /\ \E i \in unchecked[self] :
                            /\ nxt' = [nxt EXCEPT ![self] = i]
                            /\ ~ flag[i]
                       /\ pc' = [pc EXCEPT ![self] = "w2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ UNCHANGED nxt
            /\ UNCHANGED << num, flag, unchecked, max >>

w2(self) == /\ pc[self] = "w2"
            /\ IF \/ num[nxt[self]] = 0
                  \/ << num[self], self >> \prec << num[nxt[self]], nxt[self] >>
                  THEN unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {nxt[self]}]
                  ELSE UNCHANGED unchecked
            /\ pc' = [pc EXCEPT ![self] = "w1"]
            /\ UNCHANGED << num, flag, max, nxt >>

cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << num, flag, unchecked, max, nxt >>

exit(self) == /\ pc[self] = "exit"
              /\ \/ /\ \E k \in MCNat : num' = [num EXCEPT ![self] = k]
                    /\ pc' = [pc EXCEPT ![self] = "exit"]
                 \/ /\ num' = [num EXCEPT ![self] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ UNCHANGED << flag, unchecked, max, nxt >>

p(self) == \/ ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
           \/ w1(self) \/ w2(self) \/ cs(self) \/ exit(self)

Next == \E self \in Procs : p(self)

\* The ncs step is unfair (label "ncs:-"); all other steps are weakly fair.
Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ p(self))

-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
MutualExclusion == \A i, j \in Procs : (i # j) => ~ /\ pc[i] = "cs"
                                                    /\ pc[j] = "cs"

TypeOK == /\ num \in [Procs -> MCNat]
          /\ flag \in [Procs -> BOOLEAN]
          /\ unchecked \in [Procs -> SUBSET Procs]
          /\ max \in [Procs -> MCNat]
          /\ nxt \in [Procs -> Procs]
          /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4",
                               "w1", "w2", "cs", "exit"}]

Before(i, j) == /\ num[i] > 0
                /\ \/ pc[j] \in {"ncs", "e1", "exit"}
                   \/ /\ pc[j] = "e2"
                      /\ \/ i \in unchecked[j]
                         \/ max[j] >= num[i]
                   \/ /\ pc[j] = "e3"
                      /\ max[j] >= num[i]
                   \/ /\ pc[j] \in {"e4", "w1", "w2"}
                      /\ << num[i], i >> \prec << num[j], j >>
                      /\ (pc[j] \in {"w1", "w2"}) => (i \in unchecked[j])

Inv == /\ TypeOK
       /\ \A i \in Procs :
            /\ (pc[i] \in {"ncs", "e1", "e2"}) => (num[i] = 0)
            /\ (pc[i] \in {"e4", "w1", "w2", "cs"}) => (num[i] # 0)
            /\ (pc[i] \in {"e2", "e3"}) => flag[i]
            /\ (pc[i] = "w2") => (nxt[i] # i)
            /\ (pc[i] \in {"e2", "w1", "w2"}) => (i \notin unchecked[i])
            /\ (pc[i] \in {"w1", "w2"}) =>
                  \A j \in (Procs \ unchecked[i]) \ {i} : Before(i, j)
            /\ ( /\ pc[i] = "w2"
                 /\ \/ (pc[nxt[i]] = "e2") /\ (i \notin unchecked[nxt[i]])
                    \/ pc[nxt[i]] = "e3" )
               => (max[nxt[i]] >= num[i])
            /\ (pc[i] = "cs") => \A j \in Procs \ {i} : Before(i, j)

\* Liveness: every process trying to enter eventually enters.
StarvationFree == \A i \in Procs : (pc[i] = "e1") ~> (pc[i] = "cs")

\* State constraint bounding exploration: no ticket reaches MaxNat.
StateConstraint == \A i \in Procs : num[i] < MaxNat

THEOREM Spec => [](MutualExclusion /\ TypeOK /\ Inv)
=============================================================================