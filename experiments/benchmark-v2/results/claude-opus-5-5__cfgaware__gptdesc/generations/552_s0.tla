---- MODULE OneBitMutex ----
EXTENDS Integers, FiniteSets, TLC

CONSTANT N

ASSUME N \in Nat /\ N > 0

Procs == 0..(N-1)

ASSUME Procs # {}

(***************************************************************************
--algorithm OneBitMutex
 { variable x = [i \in Procs |-> FALSE] ;
   fair process (p \in Procs)
     variables unchecked = {}, other = 0 ;
     { ncs:- while (TRUE)
             { enter: x[self] := TRUE ;
                      unchecked := Procs \ {self} ;
               e2:    while (unchecked # {})
                        { with (i \in unchecked)
                            { other := i ;
                              unchecked := unchecked \ {i} } ;
                          e3: if (other < self)
                                { if (x[other])
                                    { e4: x[self] := FALSE ;
                                      e5: await ~x[other] ;
                                          goto enter } }
                              else { e6: await ~x[other] }
                        } ;
               cs:    skip ;
               exit:  x[self] := FALSE
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
        /\ other = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "enter"]
             /\ UNCHANGED << x, unchecked, other >>

enter(self) == /\ pc[self] = "enter"
               /\ x' = [x EXCEPT ![self] = TRUE]
               /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
               /\ pc' = [pc EXCEPT ![self] = "e2"]
               /\ other' = other

e2(self) == /\ pc[self] = "e2"
            /\ IF unchecked[self] # {}
                  THEN /\ \E i \in unchecked[self] :
                            /\ other' = [other EXCEPT ![self] = i]
                            /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                       /\ pc' = [pc EXCEPT ![self] = "e3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ UNCHANGED << unchecked, other >>
            /\ x' = x

e3(self) == /\ pc[self] = "e3"
            /\ IF other[self] < self
                  THEN IF x[other[self]]
                          THEN pc' = [pc EXCEPT ![self] = "e4"]
                          ELSE pc' = [pc EXCEPT ![self] = "e2"]
                  ELSE pc' = [pc EXCEPT ![self] = "e6"]
            /\ UNCHANGED << x, unchecked, other >>

e4(self) == /\ pc[self] = "e4"
            /\ x' = [x EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "e5"]
            /\ UNCHANGED << unchecked, other >>

e5(self) == /\ pc[self] = "e5"
            /\ ~x[other[self]]
            /\ pc' = [pc EXCEPT ![self] = "enter"]
            /\ UNCHANGED << x, unchecked, other >>

e6(self) == /\ pc[self] = "e6"
            /\ ~x[other[self]]
            /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ UNCHANGED << x, unchecked, other >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << x, unchecked, other >>

exit(self) == /\ pc[self] = "exit"
              /\ x' = [x EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ UNCHANGED << unchecked, other >>

p(self) == ncs(self) \/ enter(self) \/ e2(self) \/ e3(self) \/ e4(self)
              \/ e5(self) \/ e6(self) \/ cs(self) \/ exit(self)

Next == (\E self \in Procs : p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ p(self))

\* END TRANSLATION

TypeOK == /\ x \in [Procs -> BOOLEAN]
          /\ unchecked \in [Procs -> SUBSET Procs]
          /\ other \in [Procs -> Procs]
          /\ pc \in [Procs -> {"ncs", "enter", "e2", "e3", "e4", "e5", "e6", "cs", "exit"}]

MutualExclusion == \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

DeadlockFreedom ==
    (\E i \in Procs : pc[i] \notin {"ncs", "cs", "exit"})
        ~> (\E i \in Procs : pc[i] = "cs")

====