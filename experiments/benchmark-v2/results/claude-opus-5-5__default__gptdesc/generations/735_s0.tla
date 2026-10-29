------------------------------ MODULE Boulanger ------------------------------
(***************************************************************************)
(* PlusCal encoding of the Boulangerie algorithm of Yoram Moses and Katia  *)
(* Patkin, a variant of Lamport's bakery algorithm.  The module states     *)
(* type correctness and mutual exclusion as safety theorems, which were    *)
(* proved with TLAPS.  It also states deadlock freedom and starvation      *)
(* freedom as liveness properties under weak fairness.                     *)
(***************************************************************************)
EXTENDS Integers

CONSTANT N
ASSUME NAssump == N \in Nat \ {0}

Procs == 1..N

(***************************************************************************)
(* Lexicographic ordering on pairs <<ticket number, process id>>.          *)
(***************************************************************************)
a \prec b == \/ a[1] < b[1]
             \/ /\ a[1] = b[1]
                /\ a[2] < b[2]

(***************************************************************************
--algorithm Boulanger
{ variables num = [i \in Procs |-> 0], flag = [i \in Procs |-> FALSE];
  fair process (p \in Procs)
    variables unchecked = {}, max = 0, nxt = 1, previous = -1 ;
    { ncs:- while (TRUE)
            { e1:   either { flag[self] := ~ flag[self] ;
                             goto e1 }
                    or     { flag[self] := TRUE;
                             unchecked := Procs \ {self} ;
                             max := 0
                           } ;
              e2:   while (unchecked # {})
                      { with (i \in unchecked)
                          { unchecked := unchecked \ {i};
                            if (num[i] > max) { max := num[i] }
                          }
                      };
              e3:   either { with (k \in Nat) { num[self] := k } ;
                             goto e3 }
                    or     { with (i \in {j \in Nat : j > max})
                               { num[self] := i } } ;
              e4:   either { flag[self] := ~ flag[self] ;
                             goto e4 }
                    or     { flag[self] := FALSE;
                             unchecked := IF num[self] = 1
                                            THEN 1..(self-1)
                                            ELSE Procs \ {self}
                           } ;
              wa:   while (unchecked # {})
                      { with (i \in unchecked) { nxt := i };
                        await ~ flag[nxt];
                        previous := -1 ;
              wb:       if ( \/ num[nxt] = 0
                             \/ <<num[self], self>> \prec <<num[nxt], nxt>>
                             \/ /\ previous # -1
                                /\ num[nxt] # previous )
                          { unchecked := unchecked \ {nxt};
                            if (unchecked = {}) { goto cs }
                            else { goto wa }
                          }
                        else { previous := num[nxt] ;
                               goto wb }
                      } ;
              cs:   skip ;  \* critical section
              exit: either { with (k \in Nat) { num[self] := k } ;
                             goto exit }
                    or     { num[self] := 0 }
            }
    }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES num, flag, pc, unchecked, max, nxt, previous

vars == << num, flag, pc, unchecked, max, nxt, previous >>

ProcSet == Procs

Init == /\ num = [i \in Procs |-> 0]
        /\ flag = [i \in Procs |-> FALSE]
        /\ unchecked = [self \in Procs |-> {}]
        /\ max = [self \in Procs |-> 0]
        /\ nxt = [self \in Procs |-> 1]
        /\ previous = [self \in Procs |-> -1]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED << num, flag, unchecked, max, nxt, previous >>

e1(self) == /\ pc[self] = "e1"
            /\ \/ /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
                  /\ pc' = [pc EXCEPT ![self] = "e1"]
                  /\ UNCHANGED << unchecked, max >>
               \/ /\ flag' = [flag EXCEPT ![self] = TRUE]
                  /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
                  /\ max' = [max EXCEPT ![self] = 0]
                  /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ UNCHANGED << num, nxt, previous >>

e2(self) == /\ pc[self] = "e2"
            /\ IF unchecked[self] # {}
                  THEN /\ \E i \in unchecked[self]:
                            /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                            /\ IF num[i] > max[self]
                                  THEN max' = [max EXCEPT ![self] = num[i]]
                                  ELSE max' = max
                       /\ pc' = [pc EXCEPT ![self] = "e2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "e3"]
                       /\ UNCHANGED << unchecked, max >>
            /\ UNCHANGED << num, flag, nxt, previous >>

e3(self) == /\ pc[self] = "e3"
            /\ \/ /\ \E k \in Nat:
                       num' = [num EXCEPT ![self] = k]
                  /\ pc' = [pc EXCEPT ![self] = "e3"]
               \/ /\ \E i \in {j \in Nat : j > max[self]}:
                       num' = [num EXCEPT ![self] = i]
                  /\ pc' = [pc EXCEPT ![self] = "e4"]
            /\ UNCHANGED << flag, unchecked, max, nxt, previous >>

e4(self) == /\ pc[self] = "e4"
            /\ \/ /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
                  /\ pc' = [pc EXCEPT ![self] = "e4"]
                  /\ UNCHANGED unchecked
               \/ /\ flag' = [flag EXCEPT ![self] = FALSE]
                  /\ unchecked' = [unchecked EXCEPT ![self] =
                                     IF num[self] = 1
                                       THEN 1..(self-1)
                                       ELSE Procs \ {self}]
                  /\ pc' = [pc EXCEPT ![self] = "wa"]
            /\ UNCHANGED << num, max, nxt, previous >>

wa(self) == /\ pc[self] = "wa"
            /\ IF unchecked[self] # {}
                  THEN /\ \E i \in unchecked[self]:
                            nxt' = [nxt EXCEPT ![self] = i]
                       /\ ~ flag[nxt'[self]]
                       /\ previous' = [previous EXCEPT ![self] = -1]
                       /\ pc' = [pc EXCEPT ![self] = "wb"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ UNCHANGED << nxt, previous >>
            /\ UNCHANGED << num, flag, unchecked, max >>

wb(self) == /\ pc[self] = "wb"
            /\ IF \/ num[nxt[self]] = 0
                  \/ <<num[self], self>> \prec <<num[nxt[self]], nxt[self]>>
                  \/ /\ previous[self] # -1
                     /\ num[nxt[self]] # previous[self]
                  THEN /\ unchecked' = [unchecked EXCEPT ![self] =
                                          unchecked[self] \ {nxt[self]}]
                       /\ IF unchecked'[self] = {}
                             THEN pc' = [pc EXCEPT ![self] = "cs"]
                             ELSE pc' = [pc EXCEPT ![self] = "wa"]
                       /\ UNCHANGED previous
                  ELSE /\ previous' = [previous EXCEPT ![self] = num[nxt[self]]]
                       /\ pc' = [pc EXCEPT ![self] = "wb"]
                       /\ UNCHANGED unchecked
            /\ UNCHANGED << num, flag, max, nxt >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << num, flag, unchecked, max, nxt, previous >>

exit(self) == /\ pc[self] = "exit"
              /\ \/ /\ \E k \in Nat:
                         num' = [num EXCEPT ![self] = k]
                    /\ pc' = [pc EXCEPT ![self] = "exit"]
                 \/ /\ num' = [num EXCEPT ![self] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ UNCHANGED << flag, unchecked, max, nxt, previous >>

p(self) == ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
              \/ wa(self) \/ wb(self) \/ cs(self) \/ exit(self)

Next == (\E self \in Procs: p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ p(self))
\* END TRANSLATION

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
TypeOK ==
  /\ num \in [Procs -> Nat]
  /\ flag \in [Procs -> BOOLEAN]
  /\ unchecked \in [Procs -> SUBSET Procs]
  /\ max \in [Procs -> Nat]
  /\ nxt \in [Procs -> Procs]
  /\ previous \in [Procs -> Nat \cup {-1}]
  /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4",
                       "wa", "wb", "cs", "exit"}]

MutualExclusion == \A i, j \in Procs : (i # j) => ~ /\ pc[i] = "cs"
                                                    /\ pc[j] = "cs"

THEOREM TypeCorrect == Spec => []TypeOK
PROOF OMITTED

THEOREM MutualExclusionThm == Spec => []MutualExclusion
PROOF OMITTED

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)
Trying(i) == pc[i] \in {"e1", "e2", "e3", "e4", "wa", "wb"}

DeadlockFree == (\E i \in Procs : Trying(i)) ~> (\E i \in Procs : pc[i] = "cs")

StarvationFree == \A i \in Procs : (pc[i] = "e1") ~> (pc[i] = "cs")

THEOREM Liveness == Spec => DeadlockFree /\ StarvationFree
PROOF OMITTED
=============================================================================