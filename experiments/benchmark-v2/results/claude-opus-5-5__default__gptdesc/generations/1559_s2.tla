-------------------------------- MODULE LockHS --------------------------------
(***************************************************************************)
(* A two-process lock specification extended with auxiliary variables so  *)
(* that it can be shown to implement (and so be equivalent to) Peterson's  *)
(* mutual exclusion algorithm.                                             *)
(*                                                                         *)
(*  - pc     : the Lock state of each process ("r", "w", "cs").            *)
(*  - h_turn : a HISTORY variable recording the value that Peterson's     *)
(*             "turn" variable would hold.                                 *)
(*  - s      : a STUTTERING variable that splits the Lock entry into the   *)
(*             three-step entry protocol of Peterson's algorithm:          *)
(*               (1) set flag, (2) set turn, (3) wait / enter.             *)
(*             This follows the Stuttering module, modified so that the    *)
(*             stuttering step also updates the history variable h_turn.   *)
(*                                                                         *)
(* The Peterson specification is written inline, with the refinement-      *)
(* mapping substitutions already applied. This plays the role of           *)
(*   P == INSTANCE Peterson WITH pc <- pcBar, flag <- flagBar,             *)
(*                               turn <- h_turn                           *)
(* so the module parses on its own, without a separate Peterson module.    *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES pc, h_turn, s

vars     == <<pc, h_turn, s>>
lockVars == <<pc>>

Proc == {0, 1}
Other(p) == 1 - p

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK ==
  /\ pc \in [Proc -> {"r", "w", "cs"}]
  /\ h_turn \in Proc
  /\ s \in [Proc -> {"flag", "done"}]

(***************************************************************************)
(* The underlying Lock specification (without auxiliary variables).        *)
(***************************************************************************)
LInit == pc = [p \in Proc |-> "r"]

LRequest(p) ==
  /\ pc[p] = "r"
  /\ pc' = [pc EXCEPT ![p] = "w"]

LEnter(p) ==
  /\ pc[p] = "w"
  /\ pc[Other(p)] # "cs"
  /\ pc' = [pc EXCEPT ![p] = "cs"]

LExit(p) ==
  /\ pc[p] = "cs"
  /\ pc' = [pc EXCEPT ![p] = "r"]

LNext == \E p \in Proc : LRequest(p) \/ LEnter(p) \/ LExit(p)

LockSpec == LInit /\ [][LNext]_lockVars

(***************************************************************************)
(* Lock specification with the history and stuttering variables added.     *)
(***************************************************************************)
Init ==
  /\ pc = [p \in Proc |-> "r"]
  /\ h_turn \in Proc
  /\ s = [p \in Proc |-> "done"]

\* Step 1 of entry (Peterson: set flag). This is a real Lock step. The
\* stuttering variable is set so that one stuttering step must follow.
Request(p) ==
  /\ pc[p] = "r"
  /\ s[p] = "done"
  /\ pc' = [pc EXCEPT ![p] = "w"]
  /\ s'  = [s EXCEPT ![p] = "flag"]
  /\ UNCHANGED h_turn

\* Step 2 of entry (Peterson: turn := Other(p)). This is a stuttering step
\* of the Lock: pc is unchanged. The history variable records the turn.
SetTurn(p) ==
  /\ pc[p] = "w"
  /\ s[p] = "flag"
  /\ s' = [s EXCEPT ![p] = "done"]
  /\ h_turn' = Other(p)
  /\ UNCHANGED pc

\* Step 3 of entry (Peterson: await flag[q] = FALSE \/ turn = p).
Enter(p) ==
  /\ pc[p] = "w"
  /\ s[p] = "done"
  /\ pc[Other(p)] # "cs"
  /\ \/ pc[Other(p)] = "r"
     \/ h_turn = p
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ UNCHANGED <<h_turn, s>>

Exit(p) ==
  /\ pc[p] = "cs"
  /\ pc' = [pc EXCEPT ![p] = "r"]
  /\ UNCHANGED <<h_turn, s>>

Next == \E p \in Proc : Request(p) \/ SetTurn(p) \/ Enter(p) \/ Exit(p)

Fairness == \A p \in Proc : WF_vars(SetTurn(p) \/ Enter(p) \/ Exit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)
MutualExclusion == ~(pc[0] = "cs" /\ pc[1] = "cs")

\* Auxiliary invariant relating the history variable to the lock state.
\* It corresponds to Peterson's inductive invariant.
TurnInv ==
  \A p \in Proc :
     (pc[p] = "cs" /\ pc[Other(p)] = "w" /\ s[Other(p)] = "done")
        => h_turn = p

StutterInv == \A p \in Proc : s[p] = "flag" => pc[p] = "w"

Inv == TypeOK /\ MutualExclusion /\ TurnInv /\ StutterInv

(***************************************************************************)
(* Liveness: starvation freedom                                            *)
(***************************************************************************)
StarvationFree == \A p \in Proc : (pc[p] = "w") ~> (pc[p] = "cs")

DeadlockFree ==
  (\E p \in Proc : pc[p] = "w") ~> (\E p \in Proc : pc[p] = "cs")

(***************************************************************************)
(* Refinement mapping to Peterson's algorithm.                             *)
(* Peterson pc values: "r" (remainder), "f" (flag set), "t" (turn set,     *)
(* waiting), and "cs" (critical section).                                  *)
(***************************************************************************)
pcBar ==
  [p \in Proc |->
     IF pc[p] = "w"
       THEN IF s[p] = "flag" THEN "f" ELSE "t"
       ELSE pc[p]]

flagBar == [p \in Proc |-> pc[p] # "r"]

turnBar == h_turn

pVars == <<pcBar, flagBar, turnBar>>

\* Peterson's specification, with the substitutions
\*   pc <- pcBar, flag <- flagBar, turn <- turnBar (= h_turn)
P_Init ==
  /\ pcBar = [p \in Proc |-> "r"]
  /\ flagBar = [p \in Proc |-> FALSE]
  /\ turnBar \in Proc

P_SetFlag(p) ==
  /\ pcBar[p] = "r"
  /\ pcBar' = [pcBar EXCEPT ![p] = "f"]
  /\ flagBar' = [flagBar EXCEPT ![p] = TRUE]
  /\ UNCHANGED turnBar

P_SetTurn(p) ==
  /\ pcBar[p] = "f"
  /\ pcBar' = [pcBar EXCEPT ![p] = "t"]
  /\ turnBar' = Other(p)
  /\ UNCHANGED flagBar

P_Wait(p) ==
  /\ pcBar[p] = "t"
  /\ \/ flagBar[Other(p)] = FALSE
     \/ turnBar = p
  /\ pcBar' = [pcBar EXCEPT ![p] = "cs"]
  /\ UNCHANGED <<flagBar, turnBar>>

P_Exit(p) ==
  /\ pcBar[p] = "cs"
  /\ pcBar' = [pcBar EXCEPT ![p] = "r"]
  /\ flagBar' = [flagBar EXCEPT ![p] = FALSE]
  /\ UNCHANGED turnBar

P_Next == \E p \in Proc : P_SetFlag(p) \/ P_SetTurn(p) \/ P_Wait(p) \/ P_Exit(p)

P_Fairness ==
  \A p \in Proc : WF_pVars(P_SetTurn(p) \/ P_Wait(p) \/ P_Exit(p))

PetersonSpec == P_Init /\ [][P_Next]_pVars /\ P_Fairness

P_MutualExclusion == ~(pcBar[0] = "cs" /\ pcBar[1] = "cs")

(***************************************************************************)
(* Theorems                                                                *)
(***************************************************************************)
THEOREM Spec => []Inv
THEOREM Spec => LockSpec
THEOREM Spec => StarvationFree
THEOREM Spec => PetersonSpec
THEOREM Spec => []P_MutualExclusion
===============================================================================