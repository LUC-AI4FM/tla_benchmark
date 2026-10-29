------------------------------ MODULE LockHS ------------------------------
(***************************************************************************)
(* A two-process mutual-exclusion lock extended with two auxiliary         *)
(* variables, following Lamport's auxiliary-variable methodology:          *)
(*                                                                         *)
(*  - h : a history variable recording the value assigned to Peterson's    *)
(*        "turn" during the entry protocol.                                *)
(*  - s : a stuttering variable that expands each single lock Enter step   *)
(*        into three sub-steps: two pre-stuttering steps followed by the   *)
(*        real Enter step. These mirror Peterson's a1, a2, a3 steps.       *)
(*                                                                         *)
(* The stuttering is done in the standard "PreStutter" style:              *)
(*  - a stuttering sequence for Enter(p) may begin only when Enter(p) is   *)
(*    enabled;                                                             *)
(*  - while a stuttering sequence is in progress (s # top), no other       *)
(*    action may be taken;                                                 *)
(*  - the counter s.val is decremented from initVal = 2 down to            *)
(*    bot = 1, and then the real Enter(p) step is taken and s is reset     *)
(*    to top.                                                              *)
(*                                                                         *)
(* With h and s hidden, LockHS is equivalent to Lock. Under the refinement *)
(* mapping (pcBar, flagBar, turnBar), it implements Peterson's algorithm.  *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES pc,   \* Lock program counter: pc[p] \in {"a", "cs"}
          h,    \* history variable: value assigned to Peterson's turn
          s     \* stuttering variable

vars == <<pc, h, s>>

Proc == {0, 1}

Other(p) == 1 - p

(***************************************************************************)
(* The original (simple) lock specification.                               *)
(***************************************************************************)
LInit == pc = [p \in Proc |-> "a"]

LEnter(p) == /\ pc[p] = "a"
             /\ pc[Other(p)] # "cs"
             /\ pc' = [pc EXCEPT ![p] = "cs"]

LExit(p) == /\ pc[p] = "cs"
            /\ pc' = [pc EXCEPT ![p] = "a"]

LNext == \E p \in Proc : LEnter(p) \/ LExit(p)

LockSpec == LInit /\ [][LNext]_pc

(***************************************************************************)
(* Stuttering-variable conventions.                                        *)
(***************************************************************************)
top     == [id |-> "none"]   \* value of s when no stuttering is in progress
initVal == 2                 \* initial counter value of a stuttering sequence
bot     == 1                 \* counter value at which the real step occurs

StutterRec == [id : {"Enter"}, ctxt : Proc, val : {1, 2}]

(***************************************************************************)
(* The augmented lock specification.                                       *)
(***************************************************************************)
Init == /\ LInit
        /\ h \in Proc
        /\ s = top

\* Enter(p) expanded into three sub-steps (PreStutter).
EnterHS(p) ==
  IF s = top
    THEN \* first sub-step (Peterson a1): begin stuttering
         /\ ENABLED LEnter(p)
         /\ s' = [id |-> "Enter", ctxt |-> p, val |-> initVal]
         /\ UNCHANGED <<pc, h>>
    ELSE /\ s.id = "Enter"
         /\ s.ctxt = p
         /\ IF s.val = bot
              THEN \* third sub-step (Peterson a3): the real Enter step
                   /\ LEnter(p)
                   /\ s' = top
                   /\ UNCHANGED h
              ELSE \* second sub-step (Peterson a2): record turn assignment
                   /\ s' = [s EXCEPT !.val = s.val - 1]
                   /\ h' = Other(p)
                   /\ UNCHANGED pc

ExitHS(p) == /\ s = top
             /\ LExit(p)
             /\ UNCHANGED <<h, s>>

Next == \E p \in Proc : EnterHS(p) \/ ExitHS(p)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Refinement mapping to Peterson's algorithm.                             *)
(*   Peterson labels: "a1" (set flag), "a2" (set turn), "a3" (await),      *)
(*   "cs" (critical section; exiting resets flag).                         *)
(***************************************************************************)
pcBar ==
  [p \in Proc |->
     IF pc[p] = "cs" THEN "cs"
     ELSE IF s # top /\ s.ctxt = p
            THEN IF s.val = initVal THEN "a2" ELSE "a3"
            ELSE "a1"]

flagBar == [p \in Proc |-> pcBar[p] # "a1"]

turnBar == h

(***************************************************************************)
(* Peterson's specification, expressed over the mapped state functions.    *)
(***************************************************************************)
PInit == /\ pcBar = [p \in Proc |-> "a1"]
         /\ flagBar = [p \in Proc |-> FALSE]
         /\ turnBar \in Proc

Pa1(p) == /\ pcBar[p] = "a1"
          /\ flagBar' = [flagBar EXCEPT ![p] = TRUE]
          /\ pcBar' = [pcBar EXCEPT ![p] = "a2"]
          /\ UNCHANGED turnBar

Pa2(p) == /\ pcBar[p] = "a2"
          /\ turnBar' = Other(p)
          /\ pcBar' = [pcBar EXCEPT ![p] = "a3"]
          /\ UNCHANGED flagBar

Pa3(p) == /\ pcBar[p] = "a3"
          /\ (~flagBar[Other(p)] \/ turnBar = p)
          /\ pcBar' = [pcBar EXCEPT ![p] = "cs"]
          /\ UNCHANGED <<flagBar, turnBar>>

Pcs(p) == /\ pcBar[p] = "cs"
          /\ flagBar' = [flagBar EXCEPT ![p] = FALSE]
          /\ pcBar' = [pcBar EXCEPT ![p] = "a1"]
          /\ UNCHANGED turnBar

PNext == \E p \in Proc : Pa1(p) \/ Pa2(p) \/ Pa3(p) \/ Pcs(p)

PetersonSpec == PInit /\ [][PNext]_<<pcBar, flagBar, turnBar>>

(***************************************************************************)
(* Invariants.                                                             *)
(***************************************************************************)
TypeOK == /\ pc \in [Proc -> {"a", "cs"}]
          /\ h \in Proc
          /\ s \in {top} \cup StutterRec

Inv ==
  /\ TypeOK
  \* A stuttering sequence for p happens only while both processes are
  \* outside the critical section.
  /\ (s # top) => /\ pc[s.ctxt] = "a"
                  /\ pc[Other(s.ctxt)] = "a"
  \* After the second sub-step, the turn has been given to the other process.
  /\ (s # top /\ s.val = bot) => h = Other(s.ctxt)
  \* Turn ownership in Peterson terms.
  /\ \A p \in Proc : pcBar[p] = "a3" => turnBar = Other(p)
  /\ \A p \in Proc : (pcBar[p] = "cs" /\ pcBar[Other(p)] = "a3")
                         => turnBar = p

MutualExclusion == ~(pc[0] = "cs" /\ pc[1] = "cs")

PMutualExclusion == ~(pcBar[0] = "cs" /\ pcBar[1] = "cs")

(***************************************************************************)
(* Theorems.                                                               *)
(***************************************************************************)
THEOREM TypeCorrect    == Spec => []TypeOK
THEOREM Invariant      == Spec => []Inv
THEOREM Safety         == Spec => [](MutualExclusion /\ PMutualExclusion)
THEOREM RefinesLock    == Spec => LockSpec
THEOREM RefinesPeterson == Spec => PetersonSpec
=============================================================================