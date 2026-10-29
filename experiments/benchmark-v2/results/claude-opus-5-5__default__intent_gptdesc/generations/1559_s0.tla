---------------------------- MODULE PetersonLockRefinement ----------------------------
EXTENDS Naturals

(***************************************************************************)
(* Two-process mutual-exclusion lock (the low-level "Lock") with an       *)
(* auxiliary history variable h and a stuttering-control variable s,      *)
(* and its refinement to Peterson's algorithm.                            *)
(*                                                                         *)
(* In one atomic step the Lock performs the precritical flag step and the *)
(* turn assignment. Peterson performs these as two separate steps.        *)
(*   - h records the value of turn at the moment the Lock assigns it,     *)
(*     which is the value being overwritten.                              *)
(*   - s records that one extra internal (stuttering) step is pending for *)
(*     a given process.                                                    *)
(* Under the refinement mapping, the Lock's combined step corresponds to  *)
(* Peterson's flag step. The following stutter step corresponds to        *)
(* Peterson's turn assignment.                                             *)
(***************************************************************************)

Proc == {0, 1}
None == 2

Other(i) == IF i = 0 THEN 1 ELSE 0

VARIABLES pc,    \* program counter of each process
          flag,  \* flag[i] = TRUE iff process i wants to enter
          turn,  \* whose turn it is
          h,     \* history: value of turn when it was last assigned in the entry protocol
          s      \* stuttering controller: None, or the process with a pending internal step

vars == <<pc, flag, turn, h, s>>

LockPCs == {"ncs", "a1", "a3", "cs"}

-----------------------------------------------------------------------------
(* Low-level Lock with history and stuttering *)

Init ==
  /\ pc   = [i \in Proc |-> "ncs"]
  /\ flag = [i \in Proc |-> FALSE]
  /\ turn \in Proc
  /\ h    \in Proc
  /\ s    = None

\* Leave the noncritical section and begin the entry protocol.
L_ncs(i) ==
  /\ s = None
  /\ pc[i] = "ncs"
  /\ pc' = [pc EXCEPT ![i] = "a1"]
  /\ UNCHANGED <<flag, turn, h, s>>

\* Entry protocol: the precritical flag step and the turn assignment,
\* performed in one step. The history records turn as it was assigned,
\* and a stutter step is scheduled.
L_a1(i) ==
  /\ s = None
  /\ pc[i] = "a1"
  /\ flag' = [flag EXCEPT ![i] = TRUE]
  /\ turn' = Other(i)
  /\ h'    = turn
  /\ s'    = i
  /\ pc'   = [pc EXCEPT ![i] = "a3"]

\* Internal micro-step. It changes only the stuttering controller.
L_stutter(i) ==
  /\ s = i
  /\ s' = None
  /\ UNCHANGED <<pc, flag, turn, h>>

\* Wait condition, then enter the critical section.
L_a3(i) ==
  /\ s = None
  /\ pc[i] = "a3"
  /\ (~flag[Other(i)] \/ turn = i)
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED <<flag, turn, h, s>>

\* Exit step.
L_cs(i) ==
  /\ s = None
  /\ pc[i] = "cs"
  /\ flag' = [flag EXCEPT ![i] = FALSE]
  /\ pc'   = [pc EXCEPT ![i] = "ncs"]
  /\ UNCHANGED <<turn, h, s>>

LProc(i) == L_a1(i) \/ L_stutter(i) \/ L_a3(i) \/ L_cs(i)

Next == \E i \in Proc : L_ncs(i) \/ LProc(i)

Fairness == \A i \in Proc : WF_vars(LProc(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety invariants of the Lock *)

TypeOK ==
  /\ pc   \in [Proc -> LockPCs]
  /\ flag \in [Proc -> BOOLEAN]
  /\ turn \in Proc
  /\ h    \in Proc
  /\ s    \in Proc \cup {None}

MutualExclusion == ~(pc[0] = "cs" /\ pc[1] = "cs")

\* While a stutter is pending, it belongs to a process that has just
\* completed the combined flag/turn step.
StutterInv ==
  s # None => /\ pc[s] = "a3"
              /\ flag[s]
              /\ turn = Other(s)

\* When a process is in its critical section and an internal stutter is
\* active, the stutter context belongs to the other process. That
\* process has just handed the turn to the process in the critical
\* section. The recorded history value is a legal turn value, which
\* Peterson's state exposes during the stutter.
HistoryPCInv ==
  \A i \in Proc :
    (pc[i] = "cs" /\ s # None) =>
       /\ s = Other(i)
       /\ turn = i
       /\ h \in Proc
       /\ (h = Other(i) => flag[Other(i)])

\* Auxiliary inductive invariant supporting mutual exclusion.
LockInv ==
  \A i \in Proc :
    /\ (pc[i] \in {"a3", "cs"}) <=> flag[i]
    /\ (pc[i] = "cs" /\ pc[Other(i)] \in {"a3", "cs"} /\ s # Other(i))
          => turn = i

Inv == TypeOK /\ MutualExclusion /\ StutterInv /\ HistoryPCInv /\ LockInv

\* Lock liveness: a process that starts the entry protocol eventually
\* enters its critical section.
LockStarvationFree == \A i \in Proc : (pc[i] = "a1") ~> (pc[i] = "cs")

-----------------------------------------------------------------------------
(* Refinement mapping to Peterson's algorithm *)

pcBar   == [i \in Proc |-> IF s = i THEN "a2" ELSE pc[i]]
flagBar == flag
turnBar == IF s # None THEN h ELSE turn

barVars == <<pcBar, flagBar, turnBar>>

-----------------------------------------------------------------------------
(* Peterson's algorithm, expressed over the mapped state *)

PetersonPCs == {"ncs", "a1", "a2", "a3", "cs"}

P_Init ==
  /\ pcBar   = [i \in Proc |-> "ncs"]
  /\ flagBar = [i \in Proc |-> FALSE]
  /\ turnBar \in Proc

P_ncs(i) ==
  /\ pcBar[i] = "ncs"
  /\ pcBar' = [pcBar EXCEPT ![i] = "a1"]
  /\ UNCHANGED <<flagBar, turnBar>>

\* First precritical step: raise the flag.
P_a1(i) ==
  /\ pcBar[i] = "a1"
  /\ flagBar' = [flagBar EXCEPT ![i] = TRUE]
  /\ pcBar'   = [pcBar EXCEPT ![i] = "a2"]
  /\ UNCHANGED turnBar

\* Second precritical step: give the turn away.
P_a2(i) ==
  /\ pcBar[i] = "a2"
  /\ turnBar' = Other(i)
  /\ pcBar'   = [pcBar EXCEPT ![i] = "a3"]
  /\ UNCHANGED flagBar

\* Wait, then enter the critical section.
P_a3(i) ==
  /\ pcBar[i] = "a3"
  /\ (~flagBar[Other(i)] \/ turnBar = i)
  /\ pcBar' = [pcBar EXCEPT ![i] = "cs"]
  /\ UNCHANGED <<flagBar, turnBar>>

\* Exit.
P_cs(i) ==
  /\ pcBar[i] = "cs"
  /\ flagBar' = [flagBar EXCEPT ![i] = FALSE]
  /\ pcBar'   = [pcBar EXCEPT ![i] = "ncs"]
  /\ UNCHANGED turnBar

PProc(i) == P_a1(i) \/ P_a2(i) \/ P_a3(i) \/ P_cs(i)

P_Next == \E i \in Proc : P_ncs(i) \/ PProc(i)

P_Fairness == \A i \in Proc : WF_barVars(PProc(i))

PetersonSpec == P_Init /\ [][P_Next]_barVars /\ P_Fairness

P_TypeOK ==
  /\ pcBar   \in [Proc -> PetersonPCs]
  /\ flagBar \in [Proc -> BOOLEAN]
  /\ turnBar \in Proc

P_MutualExclusion == ~(pcBar[0] = "cs" /\ pcBar[1] = "cs")

P_StarvationFree == \A i \in Proc : (pcBar[i] = "a1") ~> (pcBar[i] = "cs")

-----------------------------------------------------------------------------
(* Refinement and step-correspondence properties *)

\* Each Lock step is a single Peterson step or a Peterson stutter.
\* The combined flag/turn step maps to P_a1. The internal stutter step
\* maps to P_a2, using the history to recover the turn value.
StepCorrespondence ==
  [][ \A i \in Proc :
        /\ L_ncs(i)     => P_ncs(i)
        /\ L_a1(i)      => P_a1(i)
        /\ L_stutter(i) => P_a2(i)
        /\ L_a3(i)      => P_a3(i)
        /\ L_cs(i)      => P_cs(i)
    ]_vars

\* Observable entry, critical and exit actions coincide once stuttering
\* is removed. Whenever no stutter is pending, a Peterson observable
\* action is enabled exactly when the corresponding Lock action is.
EnabledPreserved ==
  \A i \in Proc :
    s = None =>
      /\ (ENABLED P_ncs(i)) <=> (ENABLED L_ncs(i))
      /\ (ENABLED P_a1(i))  <=> (ENABLED L_a1(i))
      /\ (ENABLED P_a3(i))  <=> (ENABLED L_a3(i))
      /\ (ENABLED P_cs(i))  <=> (ENABLED L_cs(i))

\* A pending internal stutter of process i corresponds to Peterson's
\* turn-assignment step being enabled for i.
StutterEnabledPreserved ==
  \A i \in Proc : (s = i) => ((ENABLED P_a2(i)) /\ (ENABLED L_stutter(i)))

\* The Lock, with history and stuttering, implements Peterson's algorithm.
Refinement == PetersonSpec

THEOREM Spec => []Inv
THEOREM Spec => []P_TypeOK /\ []P_MutualExclusion
THEOREM Spec => StepCorrespondence
THEOREM Spec => []EnabledPreserved /\ []StutterEnabledPreserved
THEOREM Spec => Refinement
THEOREM Spec => LockStarvationFree /\ P_StarvationFree
=============================================================================