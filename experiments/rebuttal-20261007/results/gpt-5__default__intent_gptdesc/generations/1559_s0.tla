----------------------------- MODULE LockWithStutterRefinesPeterson -----------------------------

CONSTANT Proc

ASSUME TwoProc == \E a, b \in Proc: a # b /\ Proc = {a, b}

(* State domains *)
PCSet == {"idle", "pre1", "pre2", "setturn", "crit", "exit"}
StutPhaseSet == {"idle", "e1", "e2", "set"}
None == "none"

VARIABLES
  pc,          \* program counters of processes
  histTurn,    \* last recorded value assigned to 'turn' at the SetTurn point of the entry protocol
  stutActive,  \* whether an internal stuttering context is active
  stutOwner,   \* the process whose entry micro-steps are being stuttered
  stutPhase    \* symbolic phase of the entry micro-step stutter controller
  

Other(p) == CHOOSE q \in Proc: q # p

Init ==
  /\ pc = [p \in Proc |-> "idle"]
  /\ histTurn \in Proc
  /\ stutActive = FALSE
  /\ stutOwner = None
  /\ stutPhase = "idle"

(* Process-local abstract steps *)
Entry1(p) ==
  /\ p \in Proc
  /\ pc[p] = "idle"
  /\ pc' = [pc EXCEPT ![p] = "pre1"]
  /\ UNCHANGED << histTurn, stutActive, stutOwner, stutPhase >>

Entry2(p) ==
  /\ p \in Proc
  /\ pc[p] = "pre1"
  /\ pc' = [pc EXCEPT ![p] = "pre2"]
  /\ UNCHANGED << histTurn, stutActive, stutOwner, stutPhase >>

SetTurnAct(p) ==
  /\ p \in Proc
  /\ pc[p] = "pre2"
  /\ pc' = [pc EXCEPT ![p] = "setturn"]
  /\ histTurn' = Other(p)
  /\ UNCHANGED << stutActive, stutOwner, stutPhase >>

EnterCrit(p) ==
  /\ p \in Proc
  /\ pc[p] = "setturn"
  /\ (pc[Other(p)] = "idle" \/ histTurn = p)
  /\ pc' = [pc EXCEPT ![p] = "crit"]
  /\ UNCHANGED << histTurn, stutActive, stutOwner, stutPhase >>

ExitAct(p) ==
  /\ p \in Proc
  /\ pc[p] = "crit"
  /\ pc' = [pc EXCEPT ![p] = "exit"]
  /\ UNCHANGED << histTurn, stutActive, stutOwner, stutPhase >>

DoneAct(p) ==
  /\ p \in Proc
  /\ pc[p] = "exit"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED << histTurn, stutActive, stutOwner, stutPhase >>

(* Stuttering control for internal micro-steps of the entry protocol *)
StutterStart(p) ==
  /\ p \in Proc
  /\ ~stutActive
  /\ pc[p] \in {"pre1", "pre2", "setturn"}
  /\ stutActive' = TRUE
  /\ stutOwner' = p
  /\ stutPhase' \in {"e1", "e2", "set"}
  /\ UNCHANGED << pc, histTurn >>

StutterStep ==
  /\ stutActive
  /\ stutOwner \in Proc
  /\ stutPhase' \in {"e1", "e2", "set"}
  /\ stutOwner' = stutOwner
  /\ stutActive' = stutActive
  /\ UNCHANGED << pc, histTurn >>

StutterStop ==
  /\ stutActive
  /\ stutActive' = FALSE
  /\ stutOwner' = None
  /\ stutPhase' = "idle"
  /\ UNCHANGED << pc, histTurn >>

ProcStep(p) ==
  Entry1(p) \/ Entry2(p) \/ SetTurnAct(p) \/ EnterCrit(p) \/ ExitAct(p) \/ DoneAct(p)

Next ==
  \E p \in Proc: ProcStep(p)
  \/ (\E p \in Proc: StutterStart(p))
  \/ StutterStep
  \/ StutterStop

Vars == << pc, histTurn, stutActive, stutOwner, stutPhase >>

Spec == Init /\ [][Next]_Vars

(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)

TypeInv ==
  /\ pc \in [Proc -> PCSet]
  /\ histTurn \in Proc
  /\ stutActive \in BOOLEAN
  /\ stutOwner \in Proc \cup {None}
  /\ stutPhase \in StutPhaseSet

StutTypeRel ==
  /\ stutActive => /\ stutOwner \in Proc /\ stutPhase \in {"e1", "e2", "set"}

Mutex ==
  \A p, q \in Proc: p # q => ~(pc[p] = "crit" /\ pc[q] = "crit")

StutterCritInv ==
  \A p \in Proc:
    (pc[p] = "crit" /\ stutActive) =>
      /\ stutOwner = p
      /\ histTurn = Other(p)

Safety ==
  TypeInv /\ StutTypeRel /\ Mutex /\ StutterCritInv

THEOREM SafetyProps == Spec => []Safety

(***************************************************************************)
(* Refinement target: abstract Peterson algorithm (under refinement map)   *)
(***************************************************************************)

PetPCSet == {"idle", "trying", "crit", "exit"}

PcMap(P) ==
  [p \in Proc |->
    IF P[p] = "idle" THEN "idle"
    ELSE IF P[p] \in {"pre1", "pre2", "setturn"} THEN "trying"
    ELSE IF P[p] = "crit" THEN "crit"
    ELSE "exit"]

PetFlagOf(P) == [p \in Proc |-> PcMap(P)[p] # "idle"]

(* Refinement-mapped Peterson initial condition *)
PetInitRM ==
  /\ PcMap(pc) = [p \in Proc |-> "idle"]
  /\ PetFlagOf(pc) = [p \in Proc |-> FALSE]
  /\ histTurn \in Proc

(* Refinement-mapped Peterson actions (using current and next mapped values) *)
PetEntryRM(p) ==
  /\ p \in Proc
  /\ PcMap(pc)[p] = "idle"
  /\ PcMap(pc') = [PcMap(pc) EXCEPT ![p] = "trying"]
  /\ histTurn' = histTurn

PetSetTurnRM(p) ==
  /\ p \in Proc
  /\ PcMap(pc)[p] = "trying"
  /\ PcMap(pc') = PcMap(pc)
  /\ histTurn' = Other(p)

PetEnterRM(p) ==
  /\ p \in Proc
  /\ PcMap(pc)[p] = "trying"
  /\ (PetFlagOf(pc)[Other(p)] = FALSE \/ histTurn = p)
  /\ PcMap(pc') = [PcMap(pc) EXCEPT ![p] = "crit"]
  /\ histTurn' = histTurn

PetExitRM(p) ==
  /\ p \in Proc
  /\ PcMap(pc)[p] = "crit"
  /\ PcMap(pc') = [PcMap(pc) EXCEPT ![p] = "exit"]
  /\ histTurn' = histTurn

PetDoneRM(p) ==
  /\ p \in Proc
  /\ PcMap(pc)[p] = "exit"
  /\ PcMap(pc') = [PcMap(pc) EXCEPT ![p] = "idle"]
  /\ histTurn' = histTurn

PetNextRM ==
  \E p \in Proc:
       PetEntryRM(p)
    \/ PetSetTurnRM(p)
    \/ PetEnterRM(p)
    \/ PetExitRM(p)
    \/ PetDoneRM(p)

PetVarsRM == << PcMap(pc), PetFlagOf(pc), histTurn >>

PetSpecRM == PetInitRM /\ [][PetNextRM]_PetVarsRM

THEOREM Refinement == Spec => PetSpecRM

(***************************************************************************)
(* Enabledness preservation of external (observable) actions               *)
(***************************************************************************)

EnablednessPreserved ==
  [] \A p \in Proc:
    /\ (ENABLED Entry1(p)) <=> (ENABLED PetEntryRM(p))
    /\ (ENABLED EnterCrit(p)) <=> (ENABLED PetEnterRM(p))
    /\ (ENABLED ExitAct(p)) <=> (ENABLED PetExitRM(p))

================================================================================