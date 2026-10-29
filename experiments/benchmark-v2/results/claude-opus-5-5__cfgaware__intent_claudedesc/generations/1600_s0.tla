---------------------------- MODULE FastMutex ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS defaultInitValue, N

ASSUME N \in Nat /\ N >= 1

(***************************************************************************
--algorithm FastMutex {
 variables x = defaultInitValue, y = 0, b = [i \in 1..N |-> FALSE] ;
 process (Proc \in 1..N)
 variable j = defaultInitValue ;
 { ncs: while (TRUE)
        { skip ;
    start : b[self] := TRUE ;
       l1 : x := self ;
       l2 : if (y # 0)
             { l3 : b[self] := FALSE ;
               l4 : await y = 0 ;
                    goto start
             } ;
       l5 : y := self ;
       l6 : if (x # self)
             { l7 : b[self] := FALSE ;
                    j := 1 ;
               l8 : while (j \leq N)
                      { await ~b[j] ;
                        j := j+1
                      } ;
               l9 : if (y # self)
                     { l10 : await y = 0 ;
                             goto start
                     }
             } ;
       cs : skip ;
      l11 : y := 0 ;
      l12 : b[self] := FALSE
        }
 }
}
***************************************************************************)

VARIABLES x, y, b, pc, j

vars == << x, y, b, pc, j >>

ProcSet == (1..N)

Init == /\ x = defaultInitValue
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ j = [self \in 1..N |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, j >>

start(self) == /\ pc[self] = "start"
               /\ b' = [b EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "l1"]
               /\ UNCHANGED << x, y, j >>

l1(self) == /\ pc[self] = "l1"
            /\ x' = self
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << y, b, j >>

l2(self) == /\ pc[self] = "l2"
            /\ IF y # 0
                  THEN /\ pc' = [pc EXCEPT ![self] = "l3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l5"]
            /\ UNCHANGED << x, y, b, j >>

l3(self) == /\ pc[self] = "l3"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "l4"]
            /\ UNCHANGED << x, y, j >>

l4(self) == /\ pc[self] = "l4"
            /\ y = 0
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << x, y, b, j >>

l5(self) == /\ pc[self] = "l5"
            /\ y' = self
            /\ pc' = [pc EXCEPT ![self] = "l6"]
            /\ UNCHANGED << x, b, j >>

l6(self) == /\ pc[self] = "l6"
            /\ IF x # self
                  THEN /\ pc' = [pc EXCEPT ![self] = "l7"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, j >>

l7(self) == /\ pc[self] = "l7"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ j' = [j EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "l8"]
            /\ UNCHANGED << x, y >>

l8(self) == /\ pc[self] = "l8"
            /\ IF j[self] \leq N
                  THEN /\ ~b[j[self]]
                       /\ j' = [j EXCEPT ![self] = j[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "l8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l9"]
                       /\ j' = j
            /\ UNCHANGED << x, y, b >>

l9(self) == /\ pc[self] = "l9"
            /\ IF y # self
                  THEN /\ pc' = [pc EXCEPT ![self] = "l10"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, j >>

l10(self) == /\ pc[self] = "l10"
             /\ y = 0
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, j >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "l11"]
            /\ UNCHANGED << x, y, b, j >>

l11(self) == /\ pc[self] = "l11"
             /\ y' = 0
             /\ pc' = [pc EXCEPT ![self] = "l12"]
             /\ UNCHANGED << x, b, j >>

l12(self) == /\ pc[self] = "l12"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "ncs"]
             /\ UNCHANGED << x, y, j >>

Proc(self) == ncs(self) \/ start(self) \/ l1(self) \/ l2(self)
                 \/ l3(self) \/ l4(self) \/ l5(self) \/ l6(self)
                 \/ l7(self) \/ l8(self) \/ l9(self) \/ l10(self)
                 \/ cs(self) \/ l11(self) \/ l12(self)

Next == (\E self \in 1..N : Proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..N : WF_vars(Proc(self))

-----------------------------------------------------------------------------

(* Mutual exclusion *)
Invariant == \A i, k \in 1..N : (i # k) => ~((pc[i] = "cs") /\ (pc[k] = "cs"))

SomeoneInCS == \E i \in 1..N : pc[i] = "cs"

(* Some process enters the critical section infinitely often *)
Liveness == []<>SomeoneInCS

(* More than one process has announced interest *)
Contention == Cardinality({i \in 1..N : b[i]}) > 1

(* The number of processes in the critical section is always 0 or 1 *)
PossibleCounts == Cardinality({i \in ProcSet : pc[i] = "cs"}) \in 0..1

(* Reachability witness: violated when a process is in CS under contention *)
_POSSIBLE == ~(SomeoneInCS /\ Contention)

=============================================================================