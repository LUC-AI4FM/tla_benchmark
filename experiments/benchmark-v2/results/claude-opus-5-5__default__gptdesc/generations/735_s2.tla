------------------------------ MODULE Boulanger ------------------------------
(***************************************************************************)
(* A PlusCal encoding of the Boulangerie algorithm of Yoram Moses and      *)
(* Katia Patkin, a variant of Lamport's bakery algorithm.  The module      *)
(* contains the TLA+ translation of the algorithm, TLAPS proofs of type    *)
(* correctness and mutual exclusion, and liveness properties asserting     *)
(* deadlock freedom and starvation freedom under weak fairness.            *)
(***************************************************************************)
EXTENDS Integers, TLAPS

CONSTANT N
ASSUME NAssump == N \in Nat

Procs == 1..N

(***************************************************************************)
(* Lexicographic ordering on pairs <<num, id>>.                            *)
(***************************************************************************)
a \prec b == \/ a[1] < b[1]
             \/ (a[1] = b[1]) /\ (a[2] < b[2])

(***************************************************************************
--algorithm Boulanger {
    variable num = [i \in Procs |-> 0], flag = [i \in Procs |-> FALSE];
    fair process (p \in Procs)
      variables unchecked = {}, max = 0, nxt = 1, previous = -1 ;
    {
ncs:- while (TRUE)
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
                           { num[self] := i }
                       } ;
          e4:   either { flag[self] := ~ flag[self] ;
                         goto e4 }
                or     { flag[self] := FALSE;
                         unchecked := IF num[self] = 1
                                        THEN 1..(self-1)
                                        ELSE Procs \ {self}
                       } ;
          w1:   while (unchecked # {})
                  {     with (i \in unchecked) { nxt := i };
                        await ~ flag[nxt];
                        previous := -1 ;
                    w2: if ( \/ num[nxt] = 0
                             \/ <<num[self], self>> \prec <<num[nxt], nxt>>
                             \/ /\ previous # -1
                                /\ num[nxt] # previous)
                          { unchecked := unchecked \ {nxt};
                            if (unchecked = {}) { goto cs }
                            else { goto w1 }
                          }
                        else { previous := num[nxt] ;
                               goto w2 }
                  } ;
          cs:   skip ;   \* the critical section
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
                                  THEN /\ max' = [max EXCEPT ![self] = num[i]]
                                  ELSE /\ TRUE
                                       /\ max' = max
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
                  /\ pc' = [pc EXCEPT ![self] = "w1"]
            /\ UNCHANGED << num, max, nxt, previous >>

w1(self) == /\ pc[self] = "w1"
            /\ IF unchecked[self] # {}
                  THEN /\ \E i \in unchecked[self]:
                            nxt' = [nxt EXCEPT ![self] = i]
                       /\ ~ flag[nxt'[self]]
                       /\ previous' = [previous EXCEPT ![self] = -1]
                       /\ pc' = [pc EXCEPT ![self] = "w2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ UNCHANGED << nxt, previous >>
            /\ UNCHANGED << num, flag, unchecked, max >>

w2(self) == /\ pc[self] = "w2"
            /\ IF \/ num[nxt[self]] = 0
                  \/ <<num[self], self>> \prec <<num[nxt[self]], nxt[self]>>
                  \/ /\ previous[self] # -1
                     /\ num[nxt[self]] # previous[self]
                  THEN /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {nxt[self]}]
                       /\ IF unchecked'[self] = {}
                             THEN /\ pc' = [pc EXCEPT ![self] = "cs"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "w1"]
                       /\ UNCHANGED previous
                  ELSE /\ previous' = [previous EXCEPT ![self] = num[nxt[self]]]
                       /\ pc' = [pc EXCEPT ![self] = "w2"]
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
              \/ w1(self) \/ w2(self) \/ cs(self) \/ exit(self)

Next == (\E self \in Procs: p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ p(self))

\* END TRANSLATION
-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties.                                                      *)
(***************************************************************************)
MutualExclusion == \A i, j \in Procs : (i # j) => ~ /\ pc[i] = "cs"
                                                     /\ pc[j] = "cs"

TypeOK == /\ num \in [Procs -> Nat]
          /\ flag \in [Procs -> BOOLEAN]
          /\ unchecked \in [Procs -> SUBSET Procs]
          /\ max \in [Procs -> Nat]
          /\ nxt \in [Procs -> Procs]
          /\ previous \in [Procs -> Nat \cup {-1}]
          /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4",
                               "w1", "w2", "cs", "exit"}]

(***************************************************************************)
(* Before(i, j) asserts that process i, having a nonzero number, is        *)
(* guaranteed to enter its critical section before process j does.         *)
(***************************************************************************)
Before(i,j) == /\ num[i] > 0
               /\ \/ pc[j] \in {"ncs", "e1", "exit"}
                  \/ /\ pc[j] = "e2"
                     /\ \/ i \in unchecked[j]
                        \/ max[j] >= num[i]
                        \/ (j > i) /\ (max[j] + 1 = num[i])
                  \/ /\ pc[j] = "e3"
                     /\ \/ max[j] >= num[i]
                        \/ (j > i) /\ (max[j] + 1 = num[i])
                  \/ /\ pc[j] \in {"e4", "w1", "w2"}
                     /\ <<num[i],i>> \prec <<num[j],j>>
                     /\ (pc[j] \in {"w1", "w2"}) => (i \in unchecked[j])
                  \/ /\ num[i] = 1
                     /\ i < j

Inv == /\ TypeOK
       /\ \A i \in Procs :
             /\ (pc[i] \in {"ncs", "e1", "e2"}) => (num[i] = 0)
             /\ (pc[i] \in {"e4", "w1", "w2", "cs"}) => (num[i] # 0)
             /\ (pc[i] \in {"e2", "e3"}) => flag[i]
             /\ (pc[i] = "w2") => (nxt[i] # i)
             /\ (pc[i] \in {"e2", "w1", "w2"}) => i \notin unchecked[i]
             /\ (pc[i] \in {"w1", "w2"}) =>
                   \A j \in (Procs \ unchecked[i]) \ {i} : Before(i, j)
             /\ /\ (pc[i] = "w2")
                /\ \/ (pc[nxt[i]] = "e2") /\ (i \notin unchecked[nxt[i]])
                   \/ pc[nxt[i]] = "e3"
                => max[nxt[i]] >= num[i]
             /\ /\ pc[i] = "w2"
                /\ previous[i] # -1
                /\ previous[i] # num[nxt[i]]
                /\ pc[nxt[i]] \in {"e4", "w1", "w2", "cs"}
                => Before(i, nxt[i])
             /\ (pc[i] = "cs") => \A j \in Procs \ {i} : Before(i, j)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Proofs of type correctness and mutual exclusion.                        *)
(***************************************************************************)
THEOREM TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY NAssump DEF Init, TypeOK, ProcSet, Procs
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2> SUFFICES ASSUME TypeOK,
                      [Next]_vars
               PROVE  TypeOK'
    OBVIOUS
  <2>1. ASSUME NEW self \in Procs, ncs(self) PROVE TypeOK'
    BY <2>1 DEF TypeOK, ncs
  <2>2. ASSUME NEW self \in Procs, e1(self) PROVE TypeOK'
    BY <2>2 DEF TypeOK, e1
  <2>3. ASSUME NEW self \in Procs, e2(self) PROVE TypeOK'
    BY <2>3 DEF TypeOK, e2
  <2>4. ASSUME NEW self \in Procs, e3(self) PROVE TypeOK'
    BY <2>4 DEF TypeOK, e3
  <2>5. ASSUME NEW self \in Procs, e4(self) PROVE TypeOK'
    BY <2>5, NAssump DEF TypeOK, e4, Procs
  <2>6. ASSUME NEW self \in Procs, w1(self) PROVE TypeOK'
    BY <2>6 DEF TypeOK, w1
  <2>7. ASSUME NEW self \in Procs, w2(self) PROVE TypeOK'
    BY <2>7 DEF TypeOK, w2
  <2>8. ASSUME NEW self \in Procs, cs(self) PROVE TypeOK'
    BY <2>8 DEF TypeOK, cs
  <2>9. ASSUME NEW self \in Procs, exit(self) PROVE TypeOK'
    BY <2>9 DEF TypeOK, exit
  <2>10. CASE UNCHANGED vars
    BY <2>10 DEF TypeOK, vars
  <2>11. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10
       DEF Next, p
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM InvInductive == Spec => []Inv
<1> USE NAssump DEF Procs, ProcSet, \prec
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK, Before
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>1. ASSUME NEW self \in Procs, ncs(self) PROVE Inv'
    BY <2>1 DEF Inv, TypeOK, Before, ncs
  <2>2. ASSUME NEW self \in Procs, e1(self) PROVE Inv'
    BY <2>2 DEF Inv, TypeOK, Before, e1
  <2>3. ASSUME NEW self \in Procs, e2(self) PROVE Inv'
    BY <2>3 DEF Inv, TypeOK, Before, e2
  <2>4. ASSUME NEW self \in Procs, e3(self) PROVE Inv'
    BY <2>4 DEF Inv, TypeOK, Before, e3
  <2>5. ASSUME NEW self \in Procs, e4(self) PROVE Inv'
    BY <2>5 DEF Inv, TypeOK, Before, e4
  <2>6. ASSUME NEW self \in Procs, w1(self) PROVE Inv'
    BY <2>6 DEF Inv, TypeOK, Before, w1
  <2>7. ASSUME NEW self \in Procs, w2(self) PROVE Inv'
    BY <2>7 DEF Inv, TypeOK, Before, w2
  <2>8. ASSUME NEW self \in Procs, cs(self) PROVE Inv'
    BY <2>8 DEF Inv, TypeOK, Before, cs
  <2>9. ASSUME NEW self \in Procs, exit(self) PROVE Inv'
    BY <2>9 DEF Inv, TypeOK, Before, exit
  <2>10. CASE UNCHANGED vars
    BY <2>10 DEF Inv, TypeOK, Before, vars
  <2>11. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10
       DEF Next, p
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM Mutex == Spec => []MutualExclusion
<1>1. Inv => MutualExclusion
  BY DEF Inv, TypeOK, Before, MutualExclusion, \prec, Procs
<1>2. QED
  BY InvInductive, <1>1, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness properties (checked, not proved).                              *)
(***************************************************************************)
Trying(i) == pc[i] = "e1"
InCS(i)   == pc[i] = "cs"

DeadlockFree   == (\E i \in Procs : Trying(i)) ~> (\E i \in Procs : InCS(i))
StarvationFree == \A i \in Procs : Trying(i) ~> InCS(i)

THEOREM Spec => /\ DeadlockFree
                /\ StarvationFree
  PROOF OMITTED
=============================================================================