------------------------------ MODULE Peterson ------------------------------
EXTENDS Integers

(***************************************************************************)
(* Peterson's two-process mutual exclusion algorithm.                     *)
(*                                                                         *)
(* Processes are 0 and 1.  Each process loops forever:                    *)
(*   "a0" : noncritical section                                           *)
(*   "a1" : flag[self] := TRUE        (announce intent)                    *)
(*   "a2" : turn := Other(self)       (give the other process priority)   *)
(*   "a3" : await ~flag[Other(self)] \/ turn = self                       *)
(*   "cs" : critical section                                              *)
(*   "a4" : flag[self] := FALSE       (exit protocol, revoke intent)      *)
(***************************************************************************)

VARIABLES flag, turn, pc

vars == <<flag, turn, pc>>

ProcSet == {0, 1}

Other(i) == 1 - i

Labels == {"a0", "a1", "a2", "a3", "cs", "a4"}

TypeOK ==
    /\ flag \in [ProcSet -> BOOLEAN]
    /\ turn \in ProcSet
    /\ pc \in [ProcSet -> Labels]

Init ==
    /\ flag = [i \in ProcSet |-> FALSE]
    /\ turn = 0
    /\ pc = [i \in ProcSet |-> "a0"]

\* Noncritical section: proceed to the entry protocol
a0(self) ==
    /\ pc[self] = "a0"
    /\ pc' = [pc EXCEPT ![self] = "a1"]
    /\ UNCHANGED <<flag, turn>>

\* Announce intent to enter
a1(self) ==
    /\ pc[self] = "a1"
    /\ flag' = [flag EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "a2"]
    /\ UNCHANGED turn

\* Give priority to the other process
a2(self) ==
    /\ pc[self] = "a2"
    /\ turn' = Other(self)
    /\ pc' = [pc EXCEPT ![self] = "a3"]
    /\ UNCHANGED flag

\* Wait for the guard, then enter the critical section
a3(self) ==
    /\ pc[self] = "a3"
    /\ ~flag[Other(self)] \/ turn = self
    /\ pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED <<flag, turn>>

\* Critical section: leave it
cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "a4"]
    /\ UNCHANGED <<flag, turn>>

\* Exit protocol: revoke intent
a4(self) ==
    /\ pc[self] = "a4"
    /\ flag' = [flag EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "a0"]
    /\ UNCHANGED turn

Proc(self) ==
    \/ a0(self) \/ a1(self) \/ a2(self)
    \/ a3(self) \/ cs(self) \/ a4(self)

Next == \E self \in ProcSet : Proc(self)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety *)

MutualExclusion == ~(pc[0] = "cs" /\ pc[1] = "cs")

\* Flags are consistent with the control location
FlagConsistent ==
    \A i \in ProcSet : (pc[i] \in {"a2", "a3", "cs", "a4"}) <=> flag[i]

\* Inductive invariant implying mutual exclusion
Inv ==
    /\ TypeOK
    /\ FlagConsistent
    /\ \A i \in ProcSet :
         (pc[i] = "cs" /\ pc[Other(i)] \in {"a3", "cs"}) => turn = i

THEOREM InvInductive == Spec => []Inv
THEOREM Safety == Spec => []MutualExclusion

-----------------------------------------------------------------------------
(* Abstract two-process lock specification and refinement mapping.        *)
(* The abstract lock variable is either NoProc (free) or the id of the    *)
(* process holding it.                                                    *)

NoProc == -1

\* Refinement mapping: the lock is held by the process in its critical section
lockBar ==
    IF \E i \in ProcSet : pc[i] = "cs"
      THEN CHOOSE i \in ProcSet : pc[i] = "cs"
      ELSE NoProc

LInit == lockBar = NoProc

LAcquire(p) == lockBar = NoProc /\ lockBar' = p

LRelease(p) == lockBar = p /\ lockBar' = NoProc

LNext == \E p \in ProcSet : LAcquire(p) \/ LRelease(p)

LSpec == LInit /\ [][LNext]_lockBar

THEOREM Refinement == Spec => LSpec

=============================================================================