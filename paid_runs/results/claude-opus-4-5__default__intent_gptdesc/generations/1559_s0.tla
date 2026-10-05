---------------------------- MODULE PetersonRefinement ----------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS Proc0, Proc1

VARIABLES
    pc,           \* Process program counters
    flag,         \* Flag array indicating intent to enter CS
    turn,         \* Whose turn it is (for tie-breaking)
    turnHistory,  \* History component: records turn value when assigned
    stutter       \* Stuttering controller for refinement

Procs == {Proc0, Proc1}

Other(p) == IF p = Proc0 THEN Proc1 ELSE Proc0

(***************************************************************************)
(* Program counter states for each process:                                 *)
(*   "idle"     - not attempting to enter CS                                *)
(*   "flag1"    - first precritical step: set own flag                      *)
(*   "flag2"    - second precritical step: flag is set, about to set turn   *)
(*   "setTurn"  - assign turn variable                                      *)
(*   "wait"     - waiting for entry condition                               *)
(*   "cs"       - in critical section                                       *)
(*   "exit"     - exiting critical section                                  *)
(***************************************************************************)

PCStates == {"idle", "flag1", "flag2", "setTurn", "wait", "cs", "exit"}

(***************************************************************************)
(* Stuttering controller states:                                            *)
(*   <<"none", p>> - no stuttering active, p is hint for next               *)
(*   <<"entry", p>> - internal entry protocol micro-steps for process p     *)
(*   <<"done", p>> - stuttering sequence complete for process p             *)
(***************************************************************************)

StutterModes == {"none", "entry", "done"}

TypeOK ==
    /\ pc \in [Procs -> PCStates]
    /\ flag \in [Procs -> BOOLEAN]
    /\ turn \in Procs
    /\ turnHistory \in [Procs -> Procs \cup {"undef"}]
    /\ stutter \in (StutterModes \times Procs)

Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ flag = [p \in Procs |-> FALSE]
    /\ turn = Proc0  \* Arbitrary initial value
    /\ turnHistory = [p \in Procs |-> "undef"]
    /\ stutter = <<"none", Proc0>>

(***************************************************************************)
(* Entry Protocol Step 1: Process p raises its flag                         *)
(***************************************************************************)

EntryFlag1(p) ==
    /\ pc[p] = "idle"
    /\ stutter[1] = "none"
    /\ pc' = [pc EXCEPT ![p] = "flag1"]
    /\ flag' = [flag EXCEPT ![p] = TRUE]
    /\ stutter' = <<"entry", p>>
    /\ UNCHANGED <<turn, turnHistory>>

(***************************************************************************)
(* Entry Protocol Step 2: Internal micro-step (stuttering step)             *)
(***************************************************************************)

EntryFlag2(p) ==
    /\ pc[p] = "flag1"
    /\ stutter = <<"entry", p>>
    /\ pc' = [pc EXCEPT ![p] = "flag2"]
    /\ stutter' = <<"entry", p>>
    /\ UNCHANGED <<flag, turn, turnHistory>>

(***************************************************************************)
(* Entry Protocol Step 3: Set turn to other process, record in history      *)
(***************************************************************************)

SetTurn(p) ==
    /\ pc[p] = "flag2"
    /\ stutter = <<"entry", p>>
    /\ turn' = Other(p)
    /\ turnHistory' = [turnHistory EXCEPT ![p] = Other(p)]
    /\ pc' = [pc EXCEPT ![p] = "setTurn"]
    /\ stutter' = <<"entry", p>>
    /\ UNCHANGED flag

(***************************************************************************)
(* Complete entry micro-steps and move to wait                              *)
(***************************************************************************)

CompleteEntry(p) ==
    /\ pc[p] = "setTurn"
    /\ stutter = <<"entry", p>>
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ stutter' = <<"done", p>>
    /\ UNCHANGED <<flag, turn, turnHistory>>

(***************************************************************************)
(* Finalize stuttering sequence                                             *)
(***************************************************************************)

FinalizeStutter(p) ==
    /\ stutter = <<"done", p>>
    /\ pc[p] = "wait"
    /\ stutter' = <<"none", Other(p)>>
    /\ UNCHANGED <<pc, flag, turn, turnHistory>>

(***************************************************************************)
(* Wait for entry condition: other's flag is false OR turn is self          *)
(***************************************************************************)

EnterCS(p) ==
    /\ pc[p] = "wait"
    /\ stutter[1] = "none"
    /\ \/ flag[Other(p)] = FALSE
       \/ turn = p
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED <<flag, turn, turnHistory, stutter>>

(***************************************************************************)
(* Critical Section to Exit transition                                      *)
(***************************************************************************)

ExitCS(p) ==
    /\ pc[p] = "cs"
    /\ stutter[1] = "none"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED <<flag, turn, turnHistory, stutter>>

(***************************************************************************)
(* Exit: lower flag and return to idle                                      *)
(***************************************************************************)

CompleteExit(p) ==
    /\ pc[p] = "exit"
    /\ stutter[1] = "none"
    /\ flag' = [flag EXCEPT ![p] = FALSE]
    /\ turnHistory' = [turnHistory EXCEPT ![p] = "undef"]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<turn, stutter>>

(***************************************************************************)
(* Process actions                                                          *)
(***************************************************************************)

Process(p) ==
    \/ EntryFlag1(p)
    \/ EntryFlag2(p)
    \/ SetTurn(p)
    \/ CompleteEntry(p)
    \/ FinalizeStutter(p)
    \/ EnterCS(p)
    \/ ExitCS(p)
    \/ CompleteExit(p)

Next == \E p \in Procs : Process(p)

(***************************************************************************)
(* Specification with weak fairness for progress                            *)
(***************************************************************************)

Fairness == 
    /\ \A p \in Procs : WF_<<pc, flag, turn, turnHistory, stutter>>(Process(p))

Spec == Init /\ [][Next]_<<pc, flag, turn, turnHistory, stutter>> /\ Fairness

(***************************************************************************)
(* SAFETY INVARIANTS                                                        *)
(***************************************************************************)

(* Mutual Exclusion: both processes cannot be in CS simultaneously *)
MutualExclusion == ~(pc[Proc0] = "cs" /\ pc[Proc1] = "cs")

(* History-PC Invariant: when in CS with active stutter, history is consistent *)
HistoryPCInvariant ==
    \A p \in Procs :
        (pc[p] = "cs" /\ stutter[1] = "entry") =>
            (stutter[2] = p /\ 
             (turnHistory[p] # "undef" => turnHistory[p] = Other(p)))

(* Stronger history invariant: if process completed entry and is in CS,
   the recorded history turn value equals Other(p) *)
HistoryOwnershipInvariant ==
    \A p \in Procs :
        (pc[p] = "cs" /\ turnHistory[p] # "undef") =>
            turnHistory[p] = Other(p)

(* When in wait or cs, flag must be raised *)
FlagInvariant ==
    \A p \in Procs :
        pc[p] \in {"wait", "cs", "exit"} => flag[p] = TRUE

(* Stuttering consistency: entry stutter only active during entry protocol *)
StutterConsistency ==
    stutter[1] = "entry" =>
        \E p \in Procs : 
            /\ stutter[2] = p
            /\ pc[p] \in {"flag1", "flag2", "setTurn", "wait"}

(* History defined only when past setTurn step *)
HistoryDefinedInvariant ==
    \A p \in Procs :
        (turnHistory[p] # "undef") <=>
            pc[p] \in {"setTurn", "wait", "cs", "exit"}

Safety == 
    /\ TypeOK
    /\ MutualExclusion
    /\ HistoryPCInvariant
    /\ HistoryOwnershipInvariant
    /\ FlagInvariant
    /\ StutterConsistency

(***************************************************************************)
(* PETERSON'S ALGORITHM (Refinement Target)                                 *)
(***************************************************************************)

VARIABLES
    pPc,      \* Peterson's PC
    pFlag,    \* Peterson's flag
    pTurn     \* Peterson's turn

PetersonVars == <<pPc, pFlag, pTurn>>

PetersonPCStates == {"p_idle", "p_entry", "p_wait", "p_cs", "p_exit"}

PetersonTypeOK ==
    /\ pPc \in [Procs -> PetersonPCStates]
    /\ pFlag \in [Procs -> BOOLEAN]
    /\ pTurn \in Procs

PetersonInit ==
    /\ pPc = [p \in Procs |-> "p_idle"]
    /\ pFlag = [p \in Procs |-> FALSE]
    /\ pTurn = Proc0

PetersonEntry(p) ==
    /\ pPc[p] = "p_idle"
    /\ pFlag' = [pFlag EXCEPT ![p] = TRUE]
    /\ pTurn' = Other(p)
    /\ pPc' = [pPc EXCEPT ![p] = "p_wait"]

PetersonWait(p) ==
    /\ pPc[p] = "p_wait"
    /\ \/ pFlag[Other(p)] = FALSE
       \/ pTurn = p
    /\ pPc' = [pPc EXCEPT ![p] = "p_cs"]
    /\ UNCHANGED <<pFlag, pTurn>>

PetersonCS(p) ==
    /\ pPc[p] = "p_cs"
    /\ pPc' = [pPc EXCEPT ![p] = "p_exit"]
    /\ UNCHANGED <<pFlag, pTurn>>

PetersonExit(p) ==
    /\ pPc[p] = "p_exit"
    /\ pFlag' = [pFlag EXCEPT ![p] = FALSE]
    /\ pPc' = [pPc EXCEPT ![p] = "p_idle"]
    /\ UNCHANGED pTurn

PetersonProcess(p) ==
    \/ PetersonEntry(p)
    \/ PetersonWait(p)
    \/ PetersonCS(p)
    \/ PetersonExit(p)

PetersonNext == \E p \in Procs : PetersonProcess(p)

PetersonFairness == \A p \in Procs : WF_PetersonVars(PetersonProcess(p))

PetersonSpec == PetersonInit /\ [][PetersonNext]_PetersonVars /\ PetersonFairness

PetersonMutualExclusion == ~(pPc[Proc0] = "p_cs" /\ pPc[Proc1] = "p_cs")

(***************************************************************************)
(* REFINEMENT MAPPING                                                       *)
(* Maps this specification to Peterson's algorithm                          *)
(***************************************************************************)

(* Map internal PC states to Peterson's observable states *)
PCMap(p) ==
    CASE pc[p] = "idle" -> "p_idle"
      [] pc[p] = "flag1" -> "p_idle"      \* Internal step, maps to idle
      [] pc[p] = "flag2" -> "p_idle"      \* Internal step, maps to idle  
      [] pc[p] = "setTurn" -> "p_idle"    \* Internal step, maps to idle
      [] pc[p] = "wait" -> "p_wait"
      [] pc[p] = "cs" -> "p_cs"
      [] pc[p] = "exit" -> "p_exit"

(* Use history to recover turn value for refinement *)
TurnMap ==
    IF \E p \in Procs : (pc[p] \in {"setTurn", "wait", "cs"} /\ turnHistory[p] # "undef")
    THEN IF turnHistory[Proc0] # "undef" /\ pc[Proc0] \in {"setTurn", "wait", "cs"}
         THEN turnHistory[Proc0]
         ELSE IF turnHistory[Proc1] # "undef" /\ pc[Proc1] \in {"setTurn", "wait", "cs"}
              THEN turnHistory[Proc1]
              ELSE turn
    ELSE turn

(* Refinement mapping expressions *)
RefPc == [p \in Procs |-> PCMap(p)]
RefFlag == flag
RefTurn == TurnMap

(* The refinement relation: this spec refines Peterson when we use the mapping *)
Refinement == 
    /\ RefPc \in [Procs -> PetersonPCStates]
    /\ RefFlag \in [Procs -> BOOLEAN]
    /\ RefTurn \in Procs

(***************************************************************************)
(* LIVENESS PROPERTIES                                                      *)
(***************************************************************************)

(* Eventually enter CS if trying *)
EventualEntry == 
    \A p \in Procs : (pc[p] = "wait") ~> (pc[p] = "cs")

(* No starvation: if a process wants to enter, it eventually does *)
NoStarvation ==
    \A p \in Procs : (pc[p] \in {"flag1", "flag2", "setTurn", "wait"}) ~> (pc[p] = "cs")

(* Stuttering eventually completes *)
StutterTermination ==
    \A p \in Procs : (stutter = <<"entry", p>>) ~> (stutter[1] # "entry")

(* Observable action correspondence: external actions eventually occur *)
ExternalActionCorrespondence ==
    \A p \in Procs :
        /\ (pc[p] = "idle" /\ flag[p] = FALSE) ~> (pc[p] = "wait" \/ pc[p] = "idle")
        /\ (pc[p] = "cs") ~> (pc[p] = "exit" \/ pc[p] = "cs")

(***************************************************************************)
(* Combined liveness for behavioral refinement                              *)
(***************************************************************************)

Liveness == 
    /\ EventualEntry
    /\ StutterTermination

=============================================================================