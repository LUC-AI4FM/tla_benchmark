---------------------------- MODULE Boulanger ----------------------------
EXTENDS Integers

CONSTANT N
ASSUME N \in Nat

Procs == 1..N

LL(a, b) == \/ a[1] < b[1]
            \/ /\ a[1] = b[1]
               /\ a[2] < b[2]

VARIABLES num, flag, pc, unchecked, max, nxt, previous

vars == << num, flag, pc, unchecked, max, nxt, previous >>

Init == /\ num = [i \in Procs |-> 0]
        /\ flag = [i \in Procs |-> FALSE]
        /\ unchecked = [self \in Procs |-> {}]
        /\ max = [self \in Procs |-> 0]
        /\ nxt = [self \in Procs |-> 1]
        /\ previous = [self \in Procs |-> -1]
        /\ pc = [self \in Procs |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED << num, flag, unchecked, max, nxt, previous >>

e1(self) == /\ pc[self] = "e1"
            /\ \/ /\ \E k \in BOOLEAN : flag' = [flag EXCEPT ![self] = k]
                  /\ pc' = [pc EXCEPT ![self] = "e1"]
                  /\ UNCHANGED << unchecked, max >>
               \/ /\ flag' = [flag EXCEPT ![self] = TRUE]
                  /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
                  /\ max' = [max EXCEPT ![self] = 0]
                  /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ UNCHANGED << num, nxt, previous >>

e2(self) == /\ pc[self] = "e2"
            /\ IF unchecked[self] # {}
                  THEN /\ \E i \in unchecked[self] :
                            /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                            /\ IF num[i] > max[self]
                                  THEN max' = [max EXCEPT ![self] = num[i]]
                                  ELSE max' = max
                       /\ pc' = [pc EXCEPT ![self] = "e2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "e3"]
                       /\ UNCHANGED << unchecked, max >>
            /\ UNCHANGED << num, flag, nxt, previous >>

e3(self) == /\ pc[self] = "e3"
            /\ \/ /\ \E k \in Nat : num' = [num EXCEPT ![self] = k]
                  /\ pc' = [pc EXCEPT ![self] = "e3"]
               \/ /\ \E i \in {j \in Nat : j > max[self]} :
                        num' = [num EXCEPT ![self] = i]
                  /\ pc' = [pc EXCEPT ![self] = "e4"]
            /\ UNCHANGED << flag, unchecked, max, nxt, previous >>

e4(self) == /\ pc[self] = "e4"
            /\ \/ /\ \E k \in BOOLEAN : flag' = [flag EXCEPT ![self] = k]
                  /\ pc' = [pc EXCEPT ![self] = "e4"]
                  /\ UNCHANGED unchecked
               \/ /\ flag' = [flag EXCEPT ![self] = FALSE]
                  /\ unchecked' = [unchecked EXCEPT ![self] =
                                     IF num[self] = 1
                                       THEN 1..(self-1)
                                       ELSE Procs \ {self}]
                  /\ pc' = [pc EXCEPT ![self] = "w1"]
            /\ UNCHANGED << num, max, nxt, previous >>

w1(self) == /\ pc[self] = "w1"
            /\ IF unchecked[self] # {}
                  THEN /\ \E i \in unchecked[self] :
                            nxt' = [nxt EXCEPT ![self] = i]
                       /\ ~ flag[nxt'[self]]
                       /\ previous' = [previous EXCEPT ![self] = -1]
                       /\ pc' = [pc EXCEPT ![self] = "w2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ UNCHANGED << nxt, previous >>
            /\ UNCHANGED << num, flag, unchecked, max >>

w2(self) == /\ pc[self] = "w2"
            /\ IF \/ num[nxt[self]] = 0
                  \/ LL(<<num[self], self>>, <<num[nxt[self]], nxt[self]>>)
                  \/ /\ previous[self] # -1
                     /\ num[nxt[self]] # previous[self]
                  THEN /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {nxt[self]}]
                       /\ IF unchecked'[self] = {}
                             THEN pc' = [pc EXCEPT ![self] = "cs"]
                             ELSE pc' = [pc EXCEPT ![self] = "w1"]
                       /\ UNCHANGED previous
                  ELSE /\ previous' = [previous EXCEPT ![self] = num[nxt[self]]]
                       /\ pc' = [pc EXCEPT ![self] = "w2"]
                       /\ UNCHANGED unchecked
            /\ UNCHANGED << num, flag, max, nxt >>

cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << num, flag, unchecked, max, nxt, previous >>

exit(self) == /\ pc[self] = "exit"
              /\ \/ /\ \E k \in Nat : num' = [num EXCEPT ![self] = k]
                    /\ pc' = [pc EXCEPT ![self] = "exit"]
                 \/ /\ num' = [num EXCEPT ![self] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ UNCHANGED << flag, unchecked, max, nxt, previous >>

p(self) == ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
           \/ w1(self) \/ w2(self) \/ cs(self) \/ exit(self)

Next == \E self \in Procs : p(self)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ p(self))

-----------------------------------------------------------------------------

TypeOK == /\ num \in [Procs -> Nat]
          /\ flag \in [Procs -> BOOLEAN]
          /\ unchecked \in [Procs -> SUBSET Procs]
          /\ max \in [Procs -> Nat]
          /\ nxt \in [Procs -> Procs]
          /\ previous \in [Procs -> Nat \cup {-1}]
          /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4",
                               "w1", "w2", "cs", "exit"}]

MutualExclusion == \A i, j \in Procs : (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

Inv == /\ TypeOK
       /\ \A i \in Procs :
             /\ (pc[i] \in {"ncs", "e1", "e2"}) => (num[i] = 0)
             /\ (pc[i] \in {"e4", "w1", "w2", "cs"}) => (num[i] > 0)
             /\ (pc[i] \in {"e2", "e3"}) => flag[i]
             /\ (pc[i] \in {"ncs", "w1", "w2", "cs", "exit"}) => ~ flag[i]
       /\ MutualExclusion

Trying(i) == pc[i] \in {"e1", "e2", "e3", "e4", "w1", "w2"}
InCS(i) == pc[i] = "cs"

DeadlockFree == (\E i \in Procs : Trying(i)) ~> (\E i \in Procs : InCS(i))

StarvationFree == \A i \in Procs : Trying(i) ~> InCS(i)

=============================================================================