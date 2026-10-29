------------------------------ MODULE Bakery ------------------------------
(***************************************************************************)
(* Lamport's Bakery algorithm for mutual exclusion among N processes.     *)
(* The model assumes a crash-free, asynchronous system.  Reads and writes *)
(* of shared registers are modeled so that a process may "flicker" its    *)
(* flag and may write arbitrary values to num before settling on the      *)
(* final value.                                                           *)
(***************************************************************************)
EXTENDS Naturals, TLAPS

CONSTANT N

ASSUME NAssump == N \in Nat \ {0}

Procs == 1..N

(***************************************************************************)
(* Lexicographic ordering on pairs <<ticket number, process id>>.         *)
(***************************************************************************)
a \prec b == \/ a[1] < b[1]
             \/ (a[1] = b[1]) /\ (a[2] < b[2])

(***************************************************************************
--algorithm Bakery
{ variables num = [i \in Procs |-> 0], flag = [i \in Procs |-> FALSE];
  fair process (p \in Procs)
    variables unchecked = {}, max = 0, nxt = 1 ;
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
                } ;
         e3:   either { with (k \in Nat) { num[self] := k } ;
                        goto e3 }
               or     { with (i \in {j \in Nat : j > max})
                          { num[self] := i } } ;
         e4:   either { flag[self] := ~ flag[self] ;
                        goto e4 }
               or     { flag[self] := FALSE ;
                        unchecked := Procs \ {self}
                      } ;
         w1:   while (unchecked # {})
                {     with (i \in unchecked) { nxt := i };
                      await ~ flag[nxt];
                  w2: await \/ num[nxt] = 0
                            \/ <<num[self], self>> \prec <<num[nxt], nxt>> ;
                      unchecked := unchecked \ {nxt};
                } ;
         cs:   skip ;
         exit: either { with (k \in Nat) { num[self] := k } ;
                        goto exit }
               or     { num[self] := 0 }
       }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES num, flag, pc, unchecked, max, nxt

vars == << num, flag, pc, unchecked, max, nxt >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ num = [i \in Procs |-> 0]
        /\ flag = [i \in Procs |-> FALSE]
        (* Process p *)
        /\ unchecked = [self \in Procs |-> {}]
        /\ max = [self \in Procs |-> 0]
        /\ nxt = [self \in Procs |-> 1]
        /\ pc = [self \in ProcSet |-> "ncs"]

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
                  THEN /\ \E i \in unchecked[self]:
                            /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                            /\ IF num[i] > max[self]
                                  THEN /\ max' = [max EXCEPT ![self] = num[i]]
                                  ELSE /\ TRUE
                                       /\ max' = max
                       /\ pc' = [pc EXCEPT ![self] = "e2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "e3"]
                       /\ UNCHANGED << unchecked, max >>
            /\ UNCHANGED << num, flag, nxt >>

e3(self) == /\ pc[self] = "e3"
            /\ \/ /\ \E k \in Nat:
                       num' = [num EXCEPT ![self] = k]
                  /\ pc' = [pc EXCEPT ![self] = "e3"]
               \/ /\ \E i \in {j \in Nat : j > max[self]}:
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
                  THEN /\ \E i \in unchecked[self]:
                            nxt' = [nxt EXCEPT ![self] = i]
                       /\ ~ flag[nxt'[self]]
                       /\ pc' = [pc EXCEPT ![self] = "w2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ nxt' = nxt
            /\ UNCHANGED << num, flag, unchecked, max >>

w2(self) == /\ pc[self] = "w2"
            /\ \/ num[nxt[self]] = 0
               \/ <<num[self], self>> \prec <<num[nxt[self]], nxt[self]>>
            /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {nxt[self]}]
            /\ pc' = [pc EXCEPT ![self] = "w1"]
            /\ UNCHANGED << num, flag, max, nxt >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << num, flag, unchecked, max, nxt >>

exit(self) == /\ pc[self] = "exit"
              /\ \/ /\ \E k \in Nat:
                         num' = [num EXCEPT ![self] = k]
                    /\ pc' = [pc EXCEPT ![self] = "exit"]
                 \/ /\ num' = [num EXCEPT ![self] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ UNCHANGED << flag, unchecked, max, nxt >>

p(self) == ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
              \/ w1(self) \/ w2(self) \/ cs(self) \/ exit(self)

Next == (\E self \in Procs: p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ p(self))

\* END TRANSLATION
-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                      *)
(***************************************************************************)
MutualExclusion == \A i, j \in Procs : (i # j) => ~ /\ pc[i] = "cs"
                                                    /\ pc[j] = "cs"

TypeOK == /\ num \in [Procs -> Nat]
          /\ flag \in [Procs -> BOOLEAN]
          /\ unchecked \in [Procs -> SUBSET Procs]
          /\ max \in [Procs -> Nat]
          /\ nxt \in [Procs -> Procs]
          /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3",
                               "e4", "w1", "w2", "cs", "exit"}]

(***************************************************************************)
(* Before(i, j) asserts that if i and j were both in the waiting section, *)
(* process i would enter the critical section before process j.           *)
(***************************************************************************)
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

(***************************************************************************)
(* Inductive invariant                                                    *)
(***************************************************************************)
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
(***************************************************************************)
(* Proofs                                                                 *)
(***************************************************************************)
THEOREM TypeCorrect == Spec => []TypeOK
<1> USE NAssump DEF Procs, ProcSet
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2> SUFFICES ASSUME TypeOK, [Next]_vars PROVE TypeOK'
    OBVIOUS
  <2>1. ASSUME NEW self \in Procs, ncs(self) PROVE TypeOK'
    BY <2>1 DEF ncs, TypeOK
  <2>2. ASSUME NEW self \in Procs, e1(self) PROVE TypeOK'
    BY <2>2 DEF e1, TypeOK
  <2>3. ASSUME NEW self \in Procs, e2(self) PROVE TypeOK'
    BY <2>3 DEF e2, TypeOK
  <2>4. ASSUME NEW self \in Procs, e3(self) PROVE TypeOK'
    BY <2>4 DEF e3, TypeOK
  <2>5. ASSUME NEW self \in Procs, e4(self) PROVE TypeOK'
    BY <2>5 DEF e4, TypeOK
  <2>6. ASSUME NEW self \in Procs, w1(self) PROVE TypeOK'
    BY <2>6 DEF w1, TypeOK
  <2>7. ASSUME NEW self \in Procs, w2(self) PROVE TypeOK'
    BY <2>7 DEF w2, TypeOK
  <2>8. ASSUME NEW self \in Procs, cs(self) PROVE TypeOK'
    BY <2>8 DEF cs, TypeOK
  <2>9. ASSUME NEW self \in Procs, exit(self) PROVE TypeOK'
    BY <2>9 DEF exit, TypeOK
  <2>10. CASE UNCHANGED vars
    BY <2>10 DEF vars, TypeOK
  <2>11. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10
       DEF Next, p
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM Invariance == Spec => []Inv
<1> USE NAssump DEF Procs, ProcSet, TypeOK, Before, \prec
<1>1. Init => Inv
  BY SMT DEF Init, Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <2>1. ASSUME NEW self \in Procs, ncs(self) PROVE Inv'
    BY <2>1, SMT DEF ncs, Inv
  <2>2. ASSUME NEW self \in Procs, e1(self) PROVE Inv'
    <3>1. CASE /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
               /\ pc' = [pc EXCEPT ![self] = "e1"]
               /\ UNCHANGED << unchecked, max >>
      BY <2>2, <3>1, SMT DEF e1, Inv
    <3>2. CASE /\ flag' = [flag EXCEPT ![self] = TRUE]
               /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
               /\ max' = [max EXCEPT ![self] = 0]
               /\ pc' = [pc EXCEPT ![self] = "e2"]
      BY <2>2, <3>2, SMT DEF e1, Inv
    <3>3. QED
      BY <2>2, <3>1, <3>2 DEF e1
  <2>3. ASSUME NEW self \in Procs, e2(self) PROVE Inv'
    <3>1. CASE unchecked[self] # {}
      <4> SUFFICES ASSUME NEW i \in unchecked[self],
                          unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}],
                          IF num[i] > max[self]
                             THEN max' = [max EXCEPT ![self] = num[i]]
                             ELSE max' = max,
                          pc' = [pc EXCEPT ![self] = "e2"],
                          UNCHANGED << num, flag, nxt >>
                   PROVE  Inv'
        BY <2>3, <3>1, Zenon DEF e2
      <4>1. CASE num[i] > max[self]
        BY <4>1, SMT DEF Inv
      <4>2. CASE ~(num[i] > max[self])
        BY <4>2, SMT DEF Inv
      <4>3. QED
        BY <4>1, <4>2
    <3>2. CASE unchecked[self] = {}
      BY <2>3, <3>2, SMT DEF e2, Inv
    <3>3. QED
      BY <3>1, <3>2
  <2>4. ASSUME NEW self \in Procs, e3(self) PROVE Inv'
    <3>1. CASE /\ \E k \in Nat : num' = [num EXCEPT ![self] = k]
               /\ pc' = [pc EXCEPT ![self] = "e3"]
      BY <2>4, <3>1, SMT DEF e3, Inv
    <3>2. CASE /\ \E i \in {j \in Nat : j > max[self]} :
                     num' = [num EXCEPT ![self] = i]
               /\ pc' = [pc EXCEPT ![self] = "e4"]
      BY <2>4, <3>2, SMT DEF e3, Inv
    <3>3. QED
      BY <2>4, <3>1, <3>2 DEF e3
  <2>5. ASSUME NEW self \in Procs, e4(self) PROVE Inv'
    <3>1. CASE /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
               /\ pc' = [pc EXCEPT ![self] = "e4"]
               /\ UNCHANGED unchecked
      BY <2>5, <3>1, SMT DEF e4, Inv
    <3>2. CASE /\ flag' = [flag EXCEPT ![self] = FALSE]
               /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
               /\ pc' = [pc EXCEPT ![self] = "w1"]
      BY <2>5, <3>2, SMT DEF e4, Inv
    <3>3. QED
      BY <2>5, <3>1, <3>2 DEF e4
  <2>6. ASSUME NEW self \in Procs, w1(self) PROVE Inv'
    <3>1. CASE unchecked[self] # {}
      BY <2>6, <3>1, SMT DEF w1, Inv
    <3>2. CASE unchecked[self] = {}
      BY <2>6, <3>2, SMT DEF w1, Inv
    <3>3. QED
      BY <3>1, <3>2
  <2>7. ASSUME NEW self \in Procs, w2(self) PROVE Inv'
    BY <2>7, SMT DEF w2, Inv
  <2>8. ASSUME NEW self \in Procs, cs(self) PROVE Inv'
    BY <2>8, SMT DEF cs, Inv
  <2>9. ASSUME NEW self \in Procs, exit(self) PROVE Inv'
    <3>1. CASE /\ \E k \in Nat : num' = [num EXCEPT ![self] = k]
               /\ pc' = [pc EXCEPT ![self] = "exit"]
      BY <2>9, <3>1, SMT DEF exit, Inv
    <3>2. CASE /\ num' = [num EXCEPT ![self] = 0]
               /\ pc' = [pc EXCEPT ![self] = "ncs"]
      BY <2>9, <3>2, SMT DEF exit, Inv
    <3>3. QED
      BY <2>9, <3>1, <3>2 DEF exit
  <2>10. CASE UNCHANGED vars
    BY <2>10 DEF vars, Inv
  <2>11. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10
       DEF Next, p
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM Spec => []MutualExclusion
<1> USE NAssump DEF Procs, TypeOK, Before, \prec
<1>1. Inv => MutualExclusion
  BY SMT DEF Inv, MutualExclusion
<1>2. QED
  BY Invariance, <1>1, PTL
=============================================================================