------------------------------- MODULE Bakery -------------------------------
(***************************************************************************)
(* Lamport's Bakery algorithm for mutual exclusion among N processes.      *)
(* The algorithm is written in PlusCal; its TLA+ translation follows.      *)
(* Reads and writes of shared variables are not assumed to be atomic.      *)
(* A process writing num[self] or flag[self] may produce arbitrary         *)
(* intermediate values, which are modeled by nondeterministic choice.      *)
(* The system is asynchronous and crash-free.                              *)
(***************************************************************************)
EXTENDS Naturals, TLAPS

(***************************************************************************)
(* Lexicographic ordering on pairs <<ticket number, process id>>.          *)
(***************************************************************************)
a \prec b == \/ a[1] < b[1]
             \/ (a[1] = b[1]) /\ (a[2] < b[2])

CONSTANT N
ASSUME NAssump == N \in Nat

P == 1..N

(***************************************************************************
--algorithm Bakery
{ variable num = [i \in P |-> 0], flag = [i \in P |-> FALSE];
  fair process (p \in P)
    variables unchecked = {}, max = 0, nxt = 1;
  {
  ncs:- while (TRUE) {
  e1:     either { flag[self] := ~ flag[self] ;
                   goto e1 }
          or     { flag[self] := TRUE;
                   unchecked := P \ {self} ;
                   max := 0
                 } ;
  e2:     while (unchecked # {}) {
            with (i \in unchecked) {
              unchecked := unchecked \ {i};
              if (num[i] > max) { max := num[i] }
            }
          };
  e3:     either { with (k \in Nat) { num[self] := k } ;
                   goto e3 }
          or     { with (i \in {j \in Nat : j > max}) { num[self] := i } } ;
  e4:     either { flag[self] := ~ flag[self] ;
                   goto e4 }
          or     { flag[self] := FALSE;
                   unchecked := P \ {self}
                 } ;
  w1:     while (unchecked # {}) {
            with (i \in unchecked) { nxt := i };
            await ~ flag[nxt];
  w2:       await \/ num[nxt] = 0
                  \/ <<num[self], self>> \prec <<num[nxt], nxt>> ;
            unchecked := unchecked \ {nxt};
          } ;
  cs:     skip ;  \* the critical section
  exit:   either { with (k \in Nat) { num[self] := k } ;
                   goto exit }
          or     { num[self] := 0 }
        }
  }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES num, flag, pc, unchecked, max, nxt

vars == << num, flag, pc, unchecked, max, nxt >>

ProcSet == (P)

Init == (* Global variables *)
        /\ num = [i \in P |-> 0]
        /\ flag = [i \in P |-> FALSE]
        (* Process p *)
        /\ unchecked = [self \in P |-> {}]
        /\ max = [self \in P |-> 0]
        /\ nxt = [self \in P |-> 1]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED << num, flag, unchecked, max, nxt >>

e1(self) == /\ pc[self] = "e1"
            /\ \/ /\ flag' = [flag EXCEPT ![self] = ~ flag[self]]
                  /\ pc' = [pc EXCEPT ![self] = "e1"]
                  /\ UNCHANGED << unchecked, max >>
               \/ /\ flag' = [flag EXCEPT ![self] = TRUE]
                  /\ unchecked' = [unchecked EXCEPT ![self] = P \ {self}]
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
                  /\ unchecked' = [unchecked EXCEPT ![self] = P \ {self}]
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

Next == (\E self \in P: p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in P : WF_vars((pc[self] # "ncs") /\ p(self))

\* END TRANSLATION

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties.                                                      *)
(***************************************************************************)
MutualExclusion == \A i, j \in P : (i # j) => ~ /\ pc[i] = "cs"
                                                /\ pc[j] = "cs"

TypeOK == /\ num \in [P -> Nat]
          /\ flag \in [P -> BOOLEAN]
          /\ unchecked \in [P -> SUBSET P]
          /\ max \in [P -> Nat]
          /\ nxt \in [P -> P]
          /\ pc \in [P -> {"ncs", "e1", "e2", "e3", "e4",
                           "w1", "w2", "cs", "exit"}]

(***************************************************************************)
(* Before(i, j) asserts that process i has "priority" over process j:      *)
(* if j were to try to enter the critical section, it would wait for i.    *)
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
(* Inductive invariant.                                                    *)
(***************************************************************************)
Inv == /\ TypeOK
       /\ \A i \in P :
            /\ (pc[i] \in {"ncs", "e1", "e2"}) => (num[i] = 0)
            /\ (pc[i] \in {"e4", "w1", "w2", "cs"}) => (num[i] # 0)
            /\ (pc[i] \in {"e2", "e3"}) => flag[i]
            /\ (pc[i] = "w2") => (nxt[i] # i)
            /\ (pc[i] \in {"e2", "w1", "w2"}) => (i \notin unchecked[i])
            /\ (pc[i] \in {"w1", "w2"}) =>
                  \A j \in (P \ unchecked[i]) \ {i} : Before(i, j)
            /\ ( /\ pc[i] = "w2"
                 /\ \/ (pc[nxt[i]] = "e2") /\ (i \notin unchecked[nxt[i]])
                    \/ pc[nxt[i]] = "e3" )
               => (max[nxt[i]] >= num[i])
            /\ (pc[i] = "cs") => \A j \in P \ {i} : Before(i, j)

(***************************************************************************)
(* Liveness properties.                                                    *)
(***************************************************************************)
Trying(i) == pc[i] = "e1"
InCS(i)   == pc[i] = "cs"

DeadlockFree   == (\E i \in P : Trying(i)) ~> (\E i \in P : InCS(i))
StarvationFree == \A i \in P : Trying(i) ~> InCS(i)

-----------------------------------------------------------------------------
(***************************************************************************)
(* TLAPS proof of mutual exclusion.                                        *)
(***************************************************************************)
THEOREM TypeCorrect == Spec => []TypeOK
<1> USE NAssump DEF P
<1>1. Init => TypeOK
  BY DEF Init, TypeOK, ProcSet
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  BY SMT DEF TypeOK, Next, vars, p, ncs, e1, e2, e3, e4, w1, w2, cs, exit
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM Safety == Spec => []MutualExclusion
<1> USE NAssump DEF P
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK, ProcSet
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>1. ASSUME NEW self \in P,
               ncs(self)
        PROVE  Inv'
    BY <2>1, SMT DEF ncs, Inv, TypeOK, Before, \prec
  <2>2. ASSUME NEW self \in P,
               e1(self)
        PROVE  Inv'
    BY <2>2, SMT DEF e1, Inv, TypeOK, Before, \prec
  <2>3. ASSUME NEW self \in P,
               e2(self)
        PROVE  Inv'
    BY <2>3, SMT DEF e2, Inv, TypeOK, Before, \prec
  <2>4. ASSUME NEW self \in P,
               e3(self)
        PROVE  Inv'
    BY <2>4, SMT DEF e3, Inv, TypeOK, Before, \prec
  <2>5. ASSUME NEW self \in P,
               e4(self)
        PROVE  Inv'
    BY <2>5, SMT DEF e4, Inv, TypeOK, Before, \prec
  <2>6. ASSUME NEW self \in P,
               w1(self)
        PROVE  Inv'
    BY <2>6, SMT DEF w1, Inv, TypeOK, Before, \prec
  <2>7. ASSUME NEW self \in P,
               w2(self)
        PROVE  Inv'
    BY <2>7, SMT DEF w2, Inv, TypeOK, Before, \prec
  <2>8. ASSUME NEW self \in P,
               cs(self)
        PROVE  Inv'
    BY <2>8, SMT DEF cs, Inv, TypeOK, Before, \prec
  <2>9. ASSUME NEW self \in P,
               exit(self)
        PROVE  Inv'
    BY <2>9, SMT DEF exit, Inv, TypeOK, Before, \prec
  <2>10. CASE UNCHANGED vars
    BY <2>10 DEF vars, Inv, TypeOK, Before, \prec
  <2>11. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10
       DEF Next, p
<1>3. Inv => MutualExclusion
  BY SMT DEF Inv, MutualExclusion, TypeOK, Before, \prec, ProcSet
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================