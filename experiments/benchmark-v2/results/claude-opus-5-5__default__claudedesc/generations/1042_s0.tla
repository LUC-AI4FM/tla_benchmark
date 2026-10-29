--------------------------- MODULE DijkstraMutex ---------------------------
EXTENDS Integers

CONSTANT Proc

VARIABLES b, c, k, pc, temp

vars == << b, c, k, pc, temp >>

ProcSet == Proc

Init == /\ b = [i \in Proc |-> TRUE]
        /\ c = [i \in Proc |-> TRUE]
        /\ k \in Proc
        /\ temp = [self \in Proc |-> {}]
        /\ pc = [self \in ProcSet |-> "Li0"]

Li0(self) == /\ pc[self] = "Li0"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "Li1"]
             /\ UNCHANGED << c, k, temp >>

Li1(self) == /\ pc[self] = "Li1"
             /\ IF k # self
                   THEN pc' = [pc EXCEPT ![self] = "Li2"]
                   ELSE pc' = [pc EXCEPT ![self] = "Li4a"]
             /\ UNCHANGED << b, c, k, temp >>

Li2(self) == /\ pc[self] = "Li2"
             /\ c' = [c EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "Li3a"]
             /\ UNCHANGED << b, k, temp >>

Li3a(self) == /\ pc[self] = "Li3a"
              /\ IF b[k]
                    THEN pc' = [pc EXCEPT ![self] = "Li3b"]
                    ELSE pc' = [pc EXCEPT ![self] = "Li1"]
              /\ UNCHANGED << b, c, k, temp >>

Li3b(self) == /\ pc[self] = "Li3b"
              /\ k' = self
              /\ pc' = [pc EXCEPT ![self] = "Li1"]
              /\ UNCHANGED << b, c, temp >>

Li4a(self) == /\ pc[self] = "Li4a"
              /\ c' = [c EXCEPT ![self] = FALSE]
              /\ temp' = [temp EXCEPT ![self] = Proc \ {self}]
              /\ pc' = [pc EXCEPT ![self] = "Li4b"]
              /\ UNCHANGED << b, k >>

Li4b(self) == /\ pc[self] = "Li4b"
              /\ IF temp[self] # {}
                    THEN \E j \in temp[self] :
                            /\ temp' = [temp EXCEPT ![self] = temp[self] \ {j}]
                            /\ IF ~ c[j]
                                  THEN pc' = [pc EXCEPT ![self] = "Li1"]
                                  ELSE pc' = [pc EXCEPT ![self] = "Li4b"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                         /\ temp' = temp
              /\ UNCHANGED << b, c, k >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "Li5"]
            /\ UNCHANGED << b, c, k, temp >>

Li5(self) == /\ pc[self] = "Li5"
             /\ c' = [c EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "Li6"]
             /\ UNCHANGED << b, k, temp >>

Li6(self) == /\ pc[self] = "Li6"
             /\ b' = [b EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "ncs"]
             /\ UNCHANGED << c, k, temp >>

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "Li0"]
             /\ UNCHANGED << b, c, k, temp >>

P(self) == \/ Li0(self) \/ Li1(self) \/ Li2(self) \/ Li3a(self)
           \/ Li3b(self) \/ Li4a(self) \/ Li4b(self) \/ cs(self)
           \/ Li5(self) \/ Li6(self) \/ ncs(self)

Next == \E self \in Proc : P(self)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Proc : WF_vars(P(self))

-----------------------------------------------------------------------------

TypeOK == /\ b \in [Proc -> BOOLEAN]
          /\ c \in [Proc -> BOOLEAN]
          /\ k \in Proc
          /\ temp \in [Proc -> SUBSET Proc]
          /\ pc \in [Proc -> {"Li0", "Li1", "Li2", "Li3a", "Li3b", "Li4a",
                              "Li4b", "cs", "Li5", "Li6", "ncs"}]

MutualExclusion == \A i, j \in Proc :
                      (i # j) => ~ /\ pc[i] = "cs"
                                   /\ pc[j] = "cs"

-----------------------------------------------------------------------------

LSpec == /\ Init /\ [][Next]_vars
         /\ \A self \in Proc : WF_vars((pc[self] # "ncs") /\ P(self))

DeadlockFree == \A i \in Proc :
                   (pc[i] = "Li0") ~> (\E j \in Proc : pc[j] = "cs")

DeadlockFreedom ==
    (\E i \in Proc : pc[i] \notin {"Li5", "Li6", "ncs"})
        ~> (\E i \in Proc : pc[i] = "cs")

\* Not satisfied by this algorithm.
StarvationFree == \A i \in Proc :
                     (pc[i] = "Li0") ~> (pc[i] = "cs")

THEOREM Spec => []MutualExclusion
THEOREM Spec => DeadlockFree
THEOREM LSpec => DeadlockFreedom
=============================================================================