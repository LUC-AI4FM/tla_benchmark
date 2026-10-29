------------------------------ MODULE OneBitMutex ------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANT N

ASSUME N \in Nat \ {0}

Procs == 0..(N-1)

ASSUME Procs # {}

(***************************************************************************
--algorithm OneBitMutex {
  variable x = [i \in Procs |-> FALSE] ;
  fair process (p \in Procs)
    variables unchecked = {}, other \in Procs ;
  { ncs:- while (TRUE)
          { skip ;  \* the noncritical section
            e1: x[self] := TRUE ;
                unchecked := Procs \ {self} ;
            e2: while (unchecked # {})
                  { with (i \in unchecked) { other := i } ;
                    unchecked := unchecked \ {other} ;
                    e3: if (x[other])
                          { if (self > other)
                              { e4: x[self] := FALSE ;
                                e5: await ~x[other] ;
                                    goto e1 ;
                              }
                            else { e6: await ~x[other] }
                          }
                  } ;
            cs: skip ;  \* the critical section
            e7: x[self] := FALSE
          }
  }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES x, pc, unchecked, other

vars == << x, pc, unchecked, other >>

ProcSet == Procs

Init == /\ x = [i \in Procs |-> FALSE]
        /\ unchecked = [self \in Procs |-> {}]
        /\ other \in [Procs -> Procs]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED << x, unchecked, other >>

e1(self) == /\ pc[self] = "e1"
            /\ x' = [x EXCEPT ![self] = TRUE]
            /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
            /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ other' = other

e2(self) == /\ pc[self] = "e2"
            /\ IF unchecked[self] # {}
                  THEN /\ \E i \in unchecked[self]:
                            other' = [other EXCEPT ![self] = i]
                       /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {other'[self]}]
                       /\ pc' = [pc EXCEPT ![self] = "e3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ UNCHANGED << unchecked, other >>
            /\ x' = x

e3(self) == /\ pc[self] = "e3"
            /\ IF x[other[self]]
                  THEN /\ IF self > other[self]
                             THEN /\ pc' = [pc EXCEPT ![self] = "e4"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "e6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ UNCHANGED << x, unchecked, other >>

e4(self) == /\ pc[self] = "e4"
            /\ x' = [x EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "e5"]
            /\ UNCHANGED << unchecked, other >>

e5(self) == /\ pc[self] = "e5"
            /\ ~x[other[self]]
            /\ pc' = [pc EXCEPT ![self] = "e1"]
            /\ UNCHANGED << x, unchecked, other >>

e6(self) == /\ pc[self] = "e6"
            /\ ~x[other[self]]
            /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ UNCHANGED << x, unchecked, other >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "e7"]
            /\ UNCHANGED << x, unchecked, other >>

e7(self) == /\ pc[self] = "e7"
            /\ x' = [x EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "ncs"]
            /\ UNCHANGED << unchecked, other >>

p(self) == ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
              \/ e5(self) \/ e6(self) \/ cs(self) \/ e7(self)

Next == (\E self \in Procs: p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ p(self))

\* END TRANSLATION

-----------------------------------------------------------------------------

TypeOK == /\ x \in [Procs -> BOOLEAN]
          /\ unchecked \in [Procs -> SUBSET Procs]
          /\ other \in [Procs -> Procs]
          /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4",
                               "e5", "e6", "cs", "e7"}]

MutualExclusion == \A i, j \in Procs : (i # j) => ~ /\ pc[i] = "cs"
                                                    /\ pc[j] = "cs"

Trying(i) == pc[i] \in {"e1", "e2", "e3", "e4", "e5", "e6"}

DeadlockFree == (\E i \in Procs : Trying(i)) ~> (\E i \in Procs : pc[i] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => DeadlockFree
=============================================================================