------------------------------- MODULE LockHS -------------------------------
(***************************************************************************)
(* A Lock specification extended with auxiliary variables so that it can   *)
(* be shown to refine Peterson's mutual exclusion algorithm.               *)
(*                                                                         *)
(*   - pc     : the Lock's own variable ("ncs" or "cs" for each process).  *)
(*   - h_turn : a history variable that records the value of Peterson's    *)
(*              turn variable.                                             *)
(*   - s      : a stuttering variable. It splits the Lock's atomic Enter   *)
(*              step into Peterson's three-step entry protocol:            *)
(*                0 -> 1   (a1: set flag)          Lock stutters           *)
(*                1 -> 2   (a2: turn := other)     Lock stutters           *)
(*                2 -> 0   (a3: enter cs)          Lock's Enter step       *)
(*                                                                         *)
(* Following the Stuttering module (with modifications), the stuttering    *)
(* steps of Enter(p) are taken only while Enter(p) is enabled. The final   *)
(* step also checks the history variables, which is the modification.     *)
(* Peterson's algorithm is written inline over the refinement mapping,     *)
(* which takes the place of INSTANCE Peterson WITH ....                    *)
(***************************************************************************)
EXTENDS Naturals

Procs == {0, 1}

Other(p) == 1 - p

VARIABLES pc, h_turn, s

lockVars == <<pc>>
vars     == <<pc, h_turn, s>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK ==
  /\ pc \in [Procs -> {"ncs", "cs"}]
  /\ h_turn \in Procs
  /\ s \in [Procs -> 0..2]

-----------------------------------------------------------------------------
(***************************************************************************)
(* The underlying Lock protocol (without auxiliary variables)             *)
(***************************************************************************)
LockInit == pc = [p \in Procs |-> "ncs"]

LockEnter(p) ==
  /\ pc[p] = "ncs"
  /\ pc[Other(p)] # "cs"
  /\ pc' = [pc EXCEPT ![p] = "cs"]

LockExit(p) ==
  /\ pc[p] = "cs"
  /\ pc' = [pc EXCEPT ![p] = "ncs"]

LockNext == \E p \in Procs : LockEnter(p) \/ LockExit(p)

LockSpec == LockInit /\ [][LockNext]_lockVars

-----------------------------------------------------------------------------
(***************************************************************************)
(* The Lock protocol augmented with the history variable h_turn and the    *)
(* stuttering variable s.                                                  *)
(***************************************************************************)
Init ==
  /\ LockInit
  /\ h_turn = 0
  /\ s = [p \in Procs |-> 0]

EnterEnabled(p) == pc[p] = "ncs" /\ pc[Other(p)] # "cs"

\* First stuttering step: mimics Peterson's a1 (flag[p] := TRUE)
Stutter1(p) ==
  /\ EnterEnabled(p)
  /\ s[p] = 0
  /\ s' = [s EXCEPT ![p] = 1]
  /\ UNCHANGED <<pc, h_turn>>

\* Second stuttering step: mimics Peterson's a2 (turn := Other(p)),
\* recorded in the history variable h_turn
Stutter2(p) ==
  /\ EnterEnabled(p)
  /\ s[p] = 1
  /\ s' = [s EXCEPT ![p] = 2]
  /\ h_turn' = Other(p)
  /\ UNCHANGED pc

\* Final step: the actual Lock Enter step, mimicking Peterson's a3
Enter(p) ==
  /\ s[p] = 2
  /\ (s[Other(p)] = 0 \/ h_turn = p)
  /\ LockEnter(p)
  /\ s' = [s EXCEPT ![p] = 0]
  /\ UNCHANGED h_turn

\* Lock Exit step, mimicking Peterson's release (flag[p] := FALSE)
Exit(p) ==
  /\ LockExit(p)
  /\ UNCHANGED <<h_turn, s>>

Proc(p) == Stutter1(p) \/ Stutter2(p) \/ Enter(p) \/ Exit(p)

Next == \E p \in Procs : Proc(p)

Fairness ==
  \A p \in Procs :
     /\ SF_vars(Stutter2(p))
     /\ SF_vars(Enter(p))
     /\ WF_vars(Exit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)
MutualExclusion == ~(pc[0] = "cs" /\ pc[1] = "cs")

\* A process in its critical section is not in the middle of the entry protocol
CSNotStuttering == \A p \in Procs : pc[p] = "cs" => s[p] = 0

\* Stuttering steps take place only while the process is outside its cs
StutterInNcs == \A p \in Procs : s[p] # 0 => pc[p] = "ncs"

\* Peterson-style inductive invariant expressed with auxiliary variables
TurnInv ==
  \A p \in Procs :
     (pc[p] = "cs" /\ s[Other(p)] = 2) => h_turn = p

Inv ==
  /\ TypeOK
  /\ MutualExclusion
  /\ CSNotStuttering
  /\ StutterInNcs
  /\ TurnInv

(***************************************************************************)
(* Liveness                                                                *)
(***************************************************************************)
StarvationFree == \A p \in Procs : (s[p] # 0) ~> (pc[p] = "cs")

DeadlockFree ==
  (\E p \in Procs : s[p] # 0) ~> (\E p \in Procs : pc[p] = "cs")

-----------------------------------------------------------------------------
(***************************************************************************)
(* Refinement mapping to Peterson's algorithm                              *)
(***************************************************************************)
pcBar ==
  [p \in Procs |->
     IF pc[p] = "cs" THEN "cs"
     ELSE CASE s[p] = 0 -> "a1"
            [] s[p] = 1 -> "a2"
            [] s[p] = 2 -> "a3"]

flagBar == [p \in Procs |-> s[p] # 0 \/ pc[p] = "cs"]

turnBar == h_turn

pvars == <<pcBar, flagBar, turnBar>>

(***************************************************************************)
(* Peterson's algorithm, stated over the mapped variables                  *)
(* (this plays the role of INSTANCE Peterson WITH pc <- pcBar, ...)        *)
(***************************************************************************)
P_TypeOK ==
  /\ pcBar \in [Procs -> {"a1", "a2", "a3", "cs"}]
  /\ flagBar \in [Procs -> BOOLEAN]
  /\ turnBar \in Procs

P_Init ==
  /\ pcBar = [p \in Procs |-> "a1"]
  /\ flagBar = [p \in Procs |-> FALSE]
  /\ turnBar \in Procs

P_a1(p) ==
  /\ pcBar[p] = "a1"
  /\ flagBar' = [flagBar EXCEPT ![p] = TRUE]
  /\ pcBar' = [pcBar EXCEPT ![p] = "a2"]
  /\ turnBar' = turnBar

P_a2(p) ==
  /\ pcBar[p] = "a2"
  /\ turnBar' = Other(p)
  /\ pcBar' = [pcBar EXCEPT ![p] = "a3"]
  /\ flagBar' = flagBar

P_a3(p) ==
  /\ pcBar[p] = "a3"
  /\ (~flagBar[Other(p)] \/ turnBar = p)
  /\ pcBar' = [pcBar EXCEPT ![p] = "cs"]
  /\ UNCHANGED <<flagBar, turnBar>>

P_cs(p) ==
  /\ pcBar[p] = "cs"
  /\ flagBar' = [flagBar EXCEPT ![p] = FALSE]
  /\ pcBar' = [pcBar EXCEPT ![p] = "a1"]
  /\ turnBar' = turnBar

P_Proc(p) == P_a2(p) \/ P_a3(p) \/ P_cs(p)

P_Next == \E p \in Procs : P_a1(p) \/ P_Proc(p)

P_Spec ==
  /\ P_Init
  /\ [][P_Next]_pvars
  /\ \A p \in Procs : WF_pvars(P_Proc(p))

P_MutualExclusion == ~(pcBar[0] = "cs" /\ pcBar[1] = "cs")

-----------------------------------------------------------------------------
(***************************************************************************)
(* Theorems                                                                *)
(***************************************************************************)
THEOREM Spec => []Inv

THEOREM Spec => StarvationFree

\* Hiding the auxiliary variables yields the Lock specification
THEOREM Spec => LockSpec

\* The augmented Lock refines Peterson's algorithm under the mapping
THEOREM Spec => [](P_TypeOK /\ P_MutualExclusion)

THEOREM Spec => P_Init /\ [][P_Next]_pvars
=============================================================================