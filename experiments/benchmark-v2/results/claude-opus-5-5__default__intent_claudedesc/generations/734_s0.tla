---------------------------- MODULE Bakery ----------------------------
EXTENDS Naturals

CONSTANT N
ASSUME NAssump == N \in Nat

Procs == 1..N

(* Lexicographic ordering on <<ticket number, process id>> pairs *)
a \prec b == \/ a[1] < b[1]
             \/ (a[1] = b[1]) /\ (a[2] < b[2])

VARIABLES num, flag, pc, unchecked, max, nxt

vars == <<num, flag, pc, unchecked, max, nxt>>

Labels == {"ncs", "e1", "e2", "e3", "e4", "w1", "w2", "cs", "exit"}

Init == /\ num = [i \in Procs |-> 0]
        /\ flag = [i \in Procs |-> FALSE]
        /\ unchecked = [i \in Procs |-> {}]
        /\ max = [i \in Procs |-> 0]
        /\ nxt = [i \in Procs |-> 1]
        /\ pc = [i \in Procs |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED <<num, flag, unchecked, max, nxt>>

e1(self) == /\ pc[self] = "e1"
            /\ \/ /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
                  /\ pc' = [pc EXCEPT ![self] = "e1"]
                  /\ UNCHANGED <<unchecked, max>>
               \/ /\ flag' = [flag EXCEPT ![self] = TRUE]
                  /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
                  /\ max' = [max EXCEPT ![self] = 0]
                  /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ UNCHANGED <<num, nxt>>

e2(self) == /\ pc[self] = "e2"
            /\ IF unchecked[self] # {}
                  THEN /\ \E i \in unchecked[self] :
                            /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                            /\ IF num[i] > max[self]
                                  THEN max' = [max EXCEPT ![self] = num[i]]
                                  ELSE max' = max
                       /\ pc' = [pc EXCEPT ![self] = "e2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "e3"]
                       /\ UNCHANGED <<unchecked, max>>
            /\ UNCHANGED <<num, flag, nxt>>

e3(self) == /\ pc[self] = "e3"
            /\ \/ /\ \E k \in Nat : num' = [num EXCEPT ![self] = k]
                  /\ pc' = [pc EXCEPT ![self] = "e3"]
               \/ /\ \E i \in {j \in Nat : j > max[self]} :
                         num' = [num EXCEPT ![self] = i]
                  /\ pc' = [pc EXCEPT ![self] = "e4"]
            /\ UNCHANGED <<flag, unchecked, max, nxt>>

e4(self) == /\ pc[self] = "e4"
            /\ \/ /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
                  /\ pc' = [pc EXCEPT ![self] = "e4"]
                  /\ UNCHANGED unchecked
               \/ /\ flag' = [flag EXCEPT ![self] = FALSE]
                  /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
                  /\ pc' = [pc EXCEPT ![self] = "w1"]
            /\ UNCHANGED <<num, max, nxt>>

w1(self) == /\ pc[self] = "w1"
            /\ IF unchecked[self] # {}
                  THEN /\ \E i \in unchecked[self] :
                            nxt' = [nxt EXCEPT ![self] = i]
                       /\ ~ flag[nxt'[self]]
                       /\ pc' = [pc EXCEPT ![self] = "w2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ UNCHANGED nxt
            /\ UNCHANGED <<num, flag, unchecked, max>>

w2(self) == /\ pc[self] = "w2"
            /\ \/ num[nxt[self]] = 0
               \/ <<num[self], self>> \prec <<num[nxt[self]], nxt[self]>>
            /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {nxt[self]}]
            /\ pc' = [pc EXCEPT ![self] = "w1"]
            /\ UNCHANGED <<num, flag, max, nxt>>

cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED <<num, flag, unchecked, max, nxt>>

exit(self) == /\ pc[self] = "exit"
              /\ \/ /\ \E k \in Nat : num' = [num EXCEPT ![self] = k]
                    /\ pc' = [pc EXCEPT ![self] = "exit"]
                 \/ /\ num' = [num EXCEPT ![self] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ UNCHANGED <<flag, unchecked, max, nxt>>

p(self) == \/ ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
           \/ w1(self) \/ w2(self) \/ cs(self) \/ exit(self)

Next == \E self \in Procs : p(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ p(self))

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK == /\ num \in [Procs -> Nat]
          /\ flag \in [Procs -> BOOLEAN]
          /\ unchecked \in [Procs -> SUBSET Procs]
          /\ max \in [Procs -> Nat]
          /\ nxt \in [Procs -> Procs]
          /\ pc \in [Procs -> Labels]

MutualExclusion == \A i, j \in Procs : (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

-----------------------------------------------------------------------------
(* Inductive invariant supporting a deductive proof of mutual exclusion *)

Before(i, j) == /\ num[i] > 0
                /\ \/ pc[j] \in {"ncs", "e1", "exit"}
                   \/ /\ pc[j] = "e2"
                      /\ \/ i \in unchecked[j]
                         \/ max[j] >= num[i]
                   \/ /\ pc[j] = "e3"
                      /\ max[j] >= num[i]
                   \/ /\ pc[j] \in {"e4", "w1", "w2"}
                      /\ <<num[i], i>> \prec <<num[j], j>>
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
            /\ /\ pc[i] = "w2"
               /\ \/ (pc[nxt[i]] = "e2") /\ (i \notin unchecked[nxt[i]])
                  \/ pc[nxt[i]] = "e3"
               => max[nxt[i]] >= num[i]
            /\ (pc[i] = "cs") => \A j \in Procs \ {i} : Before(i, j)

-----------------------------------------------------------------------------
(* Liveness properties *)

Trying(i) == pc[i] \in {"e1", "e2", "e3", "e4", "w1", "w2"}

DeadlockFree == (\E i \in Procs : Trying(i)) ~> (\E i \in Procs : pc[i] = "cs")

StarvationFree == \A i \in Procs : (pc[i] = "e1") ~> (pc[i] = "cs")

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Inv
THEOREM Spec => []MutualExclusion
THEOREM Spec => DeadlockFree
THEOREM Spec => StarvationFree
=============================================================================