------------------------------ MODULE Peterson ------------------------------
(***************************************************************************)
(* Peterson's two-process mutual exclusion algorithm.                      *)
(*                                                                         *)
(* Each process i \in {0,1} loops forever through these control locations: *)
(*   "ncs" : noncritical section                                           *)
(*   "e1"  : entry, announce intent       (flag[i] := TRUE)                *)
(*   "e2"  : entry, give priority away    (turn := Other(i))               *)
(*   "e3"  : entry, wait until ~flag[Other(i)] \/ turn = i                 *)
(*   "cs"  : critical section                                              *)
(*   "ex"  : exit, revoke intent          (flag[i] := FALSE)               *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT None              \* model value meaning "nobody holds the lock"
ASSUME None \notin {0, 1}

VARIABLES flag, turn, pc

vars == <<flag, turn, pc>>

Procs == {0, 1}
Other(i) == 1 - i
Labels == {"ncs", "e1", "e2", "e3", "cs", "ex"}

TypeOK ==
  /\ flag \in [Procs -> BOOLEAN]
  /\ turn \in Procs
  /\ pc   \in [Procs -> Labels]

Init ==
  /\ flag = [i \in Procs |-> FALSE]
  /\ turn \in Procs
  /\ pc   = [i \in Procs |-> "ncs"]

(***************************************************************************)
(* Process actions                                                         *)
(***************************************************************************)
NCS(i) ==
  /\ pc[i] = "ncs"
  /\ pc' = [pc EXCEPT ![i] = "e1"]
  /\ UNCHANGED <<flag, turn>>

SetFlag(i) ==
  /\ pc[i] = "e1"
  /\ flag' = [flag EXCEPT ![i] = TRUE]
  /\ pc'   = [pc EXCEPT ![i] = "e2"]
  /\ UNCHANGED turn

SetTurn(i) ==
  /\ pc[i] = "e2"
  /\ turn' = Other(i)
  /\ pc'   = [pc EXCEPT ![i] = "e3"]
  /\ UNCHANGED flag

Wait(i) ==
  /\ pc[i] = "e3"
  /\ ~flag[Other(i)] \/ turn = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED <<flag, turn>>

CS(i) ==
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "ex"]
  /\ UNCHANGED <<flag, turn>>

Exit(i) ==
  /\ pc[i] = "ex"
  /\ flag' = [flag EXCEPT ![i] = FALSE]
  /\ pc'   = [pc EXCEPT ![i] = "ncs"]
  /\ UNCHANGED turn

Proc(i) ==
  \/ NCS(i)
  \/ SetFlag(i)
  \/ SetTurn(i)
  \/ Wait(i)
  \/ CS(i)
  \/ Exit(i)

(* Nondeterministic interleaving of the two processes *)
Next == \E i \in Procs : Proc(i)

(* Safety specification, stuttering allowed *)
Spec == Init /\ [][Next]_vars

(* Optional fair specification (the noncritical section may be left       *)
(* forever; all other steps are weakly fair).                              *)
FairProc(i) == SetFlag(i) \/ SetTurn(i) \/ Wait(i) \/ CS(i) \/ Exit(i)
FairSpec == Spec /\ \A i \in Procs : WF_vars(FairProc(i))

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
MutualExclusion == ~(pc[0] = "cs" /\ pc[1] = "cs")

(* Flags are consistent with control locations *)
FlagConsistent ==
  \A i \in Procs :
     /\ (pc[i] \in {"e2", "e3", "cs", "ex"}) => flag[i]
     /\ (pc[i] \in {"ncs", "e1"}) => ~flag[i]

(* Key Peterson property: if i is in its critical section while the other  *)
(* process is waiting or in its critical section, then turn favors i.      *)
TurnConsistent ==
  \A i \in Procs :
     (pc[i] = "cs" /\ pc[Other(i)] \in {"e3", "cs"}) => turn = i

(* Inductive invariant *)
Inv ==
  /\ TypeOK
  /\ FlagConsistent
  /\ TurnConsistent

THEOREM InitInv   == Init => Inv
THEOREM InvStep   == Inv /\ [Next]_vars => Inv'
THEOREM InvMutex  == Inv => MutualExclusion
THEOREM SafetyThm == Spec => []MutualExclusion
THEOREM InvThm    == Spec => []Inv

(* Liveness under fairness: every process that tries eventually enters CS *)
StarvationFree ==
  \A i \in Procs : (pc[i] = "e1") ~> (pc[i] = "cs")

THEOREM LivenessThm == FairSpec => StarvationFree

(***************************************************************************)
(* Abstract two-process lock specification, parameterized by the lock      *)
(* variable (or a state expression standing for it).                      *)
(***************************************************************************)
AbsTypeOK(lk) == lk \in Procs \cup {None}

AbsInit(lk) == lk = None

AbsAcquire(lk, i) == lk = None /\ lk' = i
AbsRelease(lk, i) == lk = i /\ lk' = None

AbsNext(lk) == \E i \in Procs : AbsAcquire(lk, i) \/ AbsRelease(lk, i)

AbsSpec(lk) == AbsInit(lk) /\ [][AbsNext(lk)]_lk

(***************************************************************************)
(* Refinement mapping: the abstract lock is held by the process in its     *)
(* critical section, if any.                                               *)
(***************************************************************************)
lockBar ==
  IF pc[0] = "cs" THEN 0
  ELSE IF pc[1] = "cs" THEN 1
  ELSE None

RefinementTypeOK == AbsTypeOK(lockBar)

(* Wait(i) maps to AbsAcquire(i), CS(i) maps to AbsRelease(i);            *)
(* all other steps map to abstract stuttering.                             *)
THEOREM Refinement == Spec => AbsSpec(lockBar)

AbsLockSpec == AbsSpec(lockBar)
=============================================================================