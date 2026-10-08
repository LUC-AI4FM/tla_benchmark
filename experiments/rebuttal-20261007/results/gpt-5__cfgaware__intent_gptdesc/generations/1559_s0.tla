------------------------------ MODULE LockHSRefPeterson ------------------------------

EXTENDS Naturals, TLC

(*
Two-process mutual-exclusion lock with history and explicit stuttering,
and its intended refinement relation to Peterson’s algorithm.
The module defines:
  - SpecHS: implementation with history and stuttering
  - TypeOKHS: type/domain invariants for HS state
  - LockInv: mutual exclusion safety invariant for HS state
  - InvHS: strengthened HS invariants (includes LockInv and history/stuttering relation)
  - PSpec: standard Peterson specification
  - Spec: bound to the abstract/observable spec (here chosen to equal PSpec)
*)

(***************************************************************************)
(* Basic domains and utilities                                             *)
(***************************************************************************)

PROC == {0, 1}

Other(p) == CHOOSE q \in PROC : q # p

PCStatesHS == {"idle", "pre1", "pre2", "set", "crit", "exit"}
PCStatesP  == {"idle", "trying", "crit", "exit"}

NoStut == "NoStut"

StutType == {NoStut} \cup [who : PROC, stage : 0..3]

(***************************************************************************)
(* Implementation with History and Stuttering (HS)                         *)
(***************************************************************************)

VARIABLES pc, turn, histTurn, stut

AbsFlag(p) == pc[p] \in {"pre1", "pre2", "set", "crit"}

InitHS ==
  /\ pc = [p \in PROC |-> "idle"]
  /\ turn \in PROC
  /\ histTurn = [p \in PROC |-> Other(p)]
  /\ stut = NoStut

Entry1(p) ==
  /\ p \in PROC
  /\ pc[p] = "idle"
  /\ pc' = [pc EXCEPT ![p] = "pre1"]
  /\ stut' = [who |-> p, stage |-> 1]
  /\ UNCHANGED <<turn, histTurn>>

Entry2(p) ==
  /\ p \in PROC
  /\ pc[p] = "pre1"
  /\ pc' = [pc EXCEPT ![p] = "pre2"]
  /\ stut' = [who |-> p, stage |-> 2]
  /\ UNCHANGED <<turn, histTurn>>

SetTurnA(p) ==
  /\ p \in PROC
  /\ pc[p] = "pre2"
  /\ pc' = [pc EXCEPT ![p] = "set"]
  /\ turn' = Other(p)
  /\ histTurn' = [histTurn EXCEPT ![p] = turn']
  /\ stut' = [who |-> p, stage |-> 3]

EnterCritA(p) ==
  /\ p \in PROC
  /\ pc[p] = "set"
  /\ (~AbsFlag(Other(p)) \/ turn = p)
  /\ pc' = [pc EXCEPT ![p] = "crit"]
  /\ stut' = NoStut
  /\ UNCHANGED <<turn, histTurn>>

ExitA(p) ==
  /\ p \in PROC
  /\ pc[p] = "crit"
  /\ pc' = [pc EXCEPT ![p] = "exit"]
  /\ UNCHANGED <<turn, histTurn, stut>>

DoneA(p) ==
  /\ p \in PROC
  /\ pc[p] = "exit"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<turn, histTurn, stut>>

IntStutter(p) ==
  /\ p \in PROC
  /\ stut # NoStut
  /\ stut.who = p
  /\ pc[p] \in {"pre1", "pre2", "set"}
  /\ stut' = [stut EXCEPT !.stage = IF @ < 3 THEN @ + 1 ELSE @]
  /\ UNCHANGED <<pc, turn, histTurn>>

NextHS ==
  \E p \in PROC :
       Entry1(p)
    \/ Entry2(p)
    \/ SetTurnA(p)
    \/ EnterCritA(p)
    \/ ExitA(p)
    \/ DoneA(p)
    \/ IntStutter(p)

varsHS == <<pc, turn, histTurn, stut>>

SpecHS ==
  /\ InitHS
  /\ [][NextHS]_varsHS
  /\ \A p \in PROC :
       WF_varsHS(Entry1(p) \/ Entry2(p) \/ SetTurnA(p) \/ EnterCritA(p) \/ ExitA(p) \/ DoneA(p))

(***************************************************************************)
(* HS Invariants                                                           *)
(***************************************************************************)

TypeOKHS ==
  /\ pc \in [PROC -> PCStatesHS]
  /\ turn \in PROC
  /\ histTurn \in [PROC -> PROC]
  /\ stut \in StutType

LockInv ==
  \A p \in PROC :
    \A q \in PROC :
      (p # q) => ~(pc[p] = "crit" /\ pc[q] = "crit")

HistCtxInv ==
  \A p \in PROC :
    (pc[p] = "crit" /\ stut # NoStut)
      => /\ stut.who = p
         /\ histTurn[p] = Other(p)

InvHS == TypeOKHS /\ LockInv /\ HistCtxInv

(***************************************************************************)
(* Abstraction mapping from HS to Peterson                                 *)
(***************************************************************************)

AbsPC(p) ==
  IF pc[p] = "idle" THEN "idle"
  ELSE IF pc[p] \in {"pre1", "pre2", "set"} THEN "trying"
  ELSE IF pc[p] = "crit" THEN "crit"
  ELSE "exit"

AbsTurn ==
  IF stut = NoStut THEN turn ELSE histTurn[stut.who]

(***************************************************************************)
(* Standard Peterson Specification (abstract)                               *)
(***************************************************************************)

VARIABLES ppc, pflag, pturn

InitP ==
  /\ ppc = [p \in PROC |-> "idle"]
  /\ pflag = [p \in PROC |-> FALSE]
  /\ pturn \in PROC

TryP(p) ==
  /\ p \in PROC
  /\ ppc[p] = "idle"
  /\ ppc' = [ppc EXCEPT ![p] = "trying"]
  /\ pflag' = [pflag EXCEPT ![p] = TRUE]
  /\ pturn' = Other(p)

EnterP(p) ==
  /\ p \in PROC
  /\ ppc[p] = "trying"
  /\ (~pflag[Other(p)] \/ pturn = p)
  /\ ppc' = [ppc EXCEPT ![p] = "crit"]
  /\ UNCHANGED <<pflag, pturn>>

ExitP(p) ==
  /\ p \in PROC
  /\ ppc[p] = "crit"
  /\ ppc' = [ppc EXCEPT ![p] = "exit"]
  /\ pflag' = [pflag EXCEPT ![p] = FALSE]
  /\ UNCHANGED pturn

DoneP(p) ==
  /\ p \in PROC
  /\ ppc[p] = "exit"
  /\ ppc' = [ppc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<pflag, pturn>>

NextP ==
  \E p \in PROC :
       TryP(p)
    \/ EnterP(p)
    \/ ExitP(p)
    \/ DoneP(p)

pvars == <<ppc, pflag, pturn>>

PSpec ==
  /\ InitP
  /\ [][NextP]_pvars
  /\ \A p \in PROC : WF_pvars(TryP(p) \/ EnterP(p) \/ ExitP(p) \/ DoneP(p))

(***************************************************************************)
(* Bind Spec to the abstract Peterson spec                                 *)
(***************************************************************************)

Spec == PSpec

=============================================================================