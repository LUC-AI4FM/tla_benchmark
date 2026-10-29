--------------------------- MODULE OneBitMutex ---------------------------
(***************************************************************************)
(* One-bit mutual exclusion protocol for N processes.  Each process owns  *)
(* a single boolean flag x[p].  To enter its critical section a process   *)
(* raises its flag and then scans every other process.  If it finds a     *)
(* raised flag belonging to a lower-numbered process (one that comes      *)
(* "before its own turn"), it backs off: it lowers its own flag, waits    *)
(* for the competitor's flag to drop, and starts over.  If it finds a     *)
(* raised flag belonging to a higher-numbered process, it waits for that  *)
(* flag to drop without lowering its own.                                 *)
(*                                                                         *)
(* --algorithm OneBitMutex                                                 *)
(*  { variable x = [p \in Procs |-> FALSE] ;                               *)
(*    process (P \in Procs)                                                *)
(*      variables unchecked = {}, other = CHOOSE p \in Procs : TRUE ;      *)
(*      { ncs: while (TRUE)                                                *)
(*              { skip ;  \* noncritical section                          *)
(*          e1:   x[self] := TRUE ;                                        *)
(*                unchecked := Procs \ {self} ;                            *)
(*          e2:   while (unchecked # {})                                   *)
(*                 { with (i \in unchecked) { other := i } ;              *)
(*                   unchecked := unchecked \ {other} ;                    *)
(*            e3:    if (x[other])                                         *)
(*                    { if (self > other)                                  *)
(*                       { x[self] := FALSE ;                              *)
(*                   e4:   await ~x[other] ;                               *)
(*                         goto e1 }                                       *)
(*                      else { e5: await ~x[other] }                       *)
(*                    }                                                    *)
(*                 } ;                                                     *)
(*          cs:   skip ;  \* critical section                             *)
(*          f:    x[self] := FALSE                                         *)
(*              }                                                          *)
(*      }                                                                  *)
(*  }                                                                      *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat \ {0}

Procs == 0..(N-1)

VARIABLES x, pc, unchecked, other

vars == << x, pc, unchecked, other >>

ProcSet == Procs

Init == /\ x = [p \in Procs |-> FALSE]
        /\ unchecked = [self \in Procs |-> {}]
        /\ other = [self \in Procs |-> CHOOSE p \in Procs : TRUE]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED << x, unchecked, other >>

e1(self) == /\ pc[self] = "e1"
            /\ x' = [x EXCEPT ![self] = TRUE]
            /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
            /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ UNCHANGED other

e2(self) == /\ pc[self] = "e2"
            /\ IF unchecked[self] # {}
                  THEN /\ \E i \in unchecked[self] :
                            /\ other' = [other EXCEPT ![self] = i]
                            /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                       /\ pc' = [pc EXCEPT ![self] = "e3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ UNCHANGED << unchecked, other >>
            /\ UNCHANGED x

e3(self) == /\ pc[self] = "e3"
            /\ IF x[other[self]]
                  THEN /\ IF self > other[self]
                             THEN /\ x' = [x EXCEPT ![self] = FALSE]
                                  /\ pc' = [pc EXCEPT ![self] = "e4"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "e5"]
                                  /\ x' = x
                  ELSE /\ pc' = [pc EXCEPT ![self] = "e2"]
                       /\ x' = x
            /\ UNCHANGED << unchecked, other >>

e4(self) == /\ pc[self] = "e4"
            /\ ~x[other[self]]
            /\ pc' = [pc EXCEPT ![self] = "e1"]
            /\ UNCHANGED << x, unchecked, other >>

e5(self) == /\ pc[self] = "e5"
            /\ ~x[other[self]]
            /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ UNCHANGED << x, unchecked, other >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "f"]
            /\ UNCHANGED << x, unchecked, other >>

f(self) == /\ pc[self] = "f"
           /\ x' = [x EXCEPT ![self] = FALSE]
           /\ pc' = [pc EXCEPT ![self] = "ncs"]
           /\ UNCHANGED << unchecked, other >>

P(self) == ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
              \/ e5(self) \/ cs(self) \/ f(self)

Next == (\E self \in Procs : P(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ P(self))

----------------------------------------------------------------------------
(* Type correctness *)
TypeOK == /\ x \in [Procs -> BOOLEAN]
          /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4", "e5", "cs", "f"}]
          /\ unchecked \in [Procs -> SUBSET Procs]
          /\ other \in [Procs -> Procs]

(* Safety: no two processes are in their critical sections at once *)
MutualExclusion == \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

(* Liveness: if some process is trying to enter, some process eventually does *)
Trying(p) == pc[p] \in {"e1", "e2", "e3", "e4", "e5"}

DeadlockFreedom ==
    (\E p \in Procs : Trying(p)) ~> (\E p \in Procs : pc[p] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => DeadlockFreedom
=============================================================================