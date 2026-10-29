---------------------------- MODULE LockHS ----------------------------
(***************************************************************************)
(* A two-process lock protocol with auxiliary variables added so that it  *)
(* refines Peterson's mutual exclusion algorithm.                          *)
(*                                                                         *)
(*   pc     : the lock's state for each process ("r" or "cs").             *)
(*   h_turn : a history variable that records the value Peterson's         *)
(*            `turn' variable would have been assigned.                    *)
(*   s      : a stuttering variable. It splits the lock's single Enter     *)
(*            step into Peterson's three entry steps: set flag, set turn,  *)
(*            and enter the critical section.                              *)
(*                                                                         *)
(* s = Top means no stuttering is in progress. Otherwise s.proc is the     *)
(* process doing its entry and s.ctr counts the stuttering steps taken.    *)
(* While stuttering is in progress, the stuttering process alone can take  *)
(* a step, as in the (modified) Stuttering module.                         *)
(*                                                                         *)
(* Peterson's specification is written inline. It is expressed in terms of *)
(* the refinement-mapped expressions pcBar, flagBar and turnBar. This      *)
(* plays the role of                                                       *)
(*    P == INSTANCE Peterson WITH pc <- pcBar, flag <- flagBar,            *)
(*                                turn <- turnBar                          *)
(* so the module parses on its own.                                        *)
(***************************************************************************)
EXTENDS Integers

VARIABLES pc, h_turn, s

vars == <<pc, h_turn, s>>

Procs == {0, 1}

Not(i) == IF i = 0 THEN 1 ELSE 0

NoProc == -1

Top == [proc |-> NoProc, ctr |-> 0]

SVals == {Top} \cup [proc : Procs, ctr : {1, 2}]

---------------------------------------------------------------------------
(***************************************************************************)
(* The original Lock specification (on variable pc only).                  *)
(***************************************************************************)
LockInit == pc = [p \in Procs |-> "r"]

LockEnter(p) == /\ pc[p] = "r"
                /\ pc[Not(p)] = "r"
                /\ pc' = [pc EXCEPT ![p] = "cs"]

LockExit(p) == /\ pc[p] = "cs"
               /\ pc' = [pc EXCEPT ![p] = "r"]

LockNext == \E p \in Procs : LockEnter(p) \/ LockExit(p)

LockSpec == /\ LockInit
            /\ [][LockNext]_pc
            /\ \A p \in Procs : SF_pc(LockEnter(p)) /\ WF_pc(LockExit(p))

---------------------------------------------------------------------------
(***************************************************************************)
(* The Lock specification with history variable h_turn and stuttering      *)
(* variable s.                                                             *)
(***************************************************************************)
TypeOK == /\ pc \in [Procs -> {"r", "cs"}]
          /\ h_turn \in Procs
          /\ s \in SVals

Init == /\ pc = [p \in Procs |-> "r"]
        /\ h_turn = 0
        /\ s = Top

(* First stuttering step. It is enabled exactly when LockEnter(p) is.     *)
(* It maps to Peterson's "set flag" step.                                  *)
BeginEnter(p) == /\ s = Top
                 /\ pc[p] = "r"
                 /\ pc[Not(p)] = "r"
                 /\ s' = [proc |-> p, ctr |-> 1]
                 /\ UNCHANGED <<pc, h_turn>>

(* Second stuttering step. It records the turn assignment in the history  *)
(* variable h_turn and maps to Peterson's "set turn" step.                 *)
SetTurn(p) == /\ s.proc = p
              /\ s.ctr = 1
              /\ s' = [proc |-> p, ctr |-> 2]
              /\ h_turn' = Not(p)
              /\ UNCHANGED pc

(* The real LockEnter step. It maps to Peterson's "enter cs" step.         *)
Enter(p) == /\ s.proc = p
            /\ s.ctr = 2
            /\ pc' = [pc EXCEPT ![p] = "cs"]
            /\ s' = Top
            /\ UNCHANGED h_turn

(* LockExit. It maps to Peterson's exit (flag reset).                      *)
Exit(p) == /\ s = Top
           /\ pc[p] = "cs"
           /\ pc' = [pc EXCEPT ![p] = "r"]
           /\ UNCHANGED <<h_turn, s>>

Proc(p) == BeginEnter(p) \/ SetTurn(p) \/ Enter(p) \/ Exit(p)

Next == \E p \in Procs : Proc(p)

Fairness == \A p \in Procs : /\ SF_vars(BeginEnter(p))
                             /\ WF_vars(SetTurn(p))
                             /\ WF_vars(Enter(p))
                             /\ WF_vars(Exit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(***************************************************************************)
(* Invariants and properties of LockHS.                                    *)
(***************************************************************************)
MutualExclusion == ~(pc[0] = "cs" /\ pc[1] = "cs")

StutterInv == s # Top => /\ pc[s.proc] = "r"
                         /\ pc[Not(s.proc)] = "r"

Inv == TypeOK /\ MutualExclusion /\ StutterInv

StarvationFree == \A p \in Procs : (s.proc = p) ~> (pc[p] = "cs")

---------------------------------------------------------------------------
(***************************************************************************)
(* Refinement mapping to Peterson's algorithm.                             *)
(***************************************************************************)
pcBar == [p \in Procs |->
            IF s.proc = p
              THEN IF s.ctr = 1 THEN "a1" ELSE "a2"
              ELSE pc[p]]

flagBar == [p \in Procs |-> pcBar[p] # "r"]

turnBar == h_turn

(***************************************************************************)
(* Peterson's algorithm, stated over the mapped variables.                 *)
(***************************************************************************)
PVars == <<pcBar, flagBar, turnBar>>

PInit == /\ pcBar = [i \in Procs |-> "r"]
         /\ flagBar = [i \in Procs |-> FALSE]
         /\ turnBar \in Procs

PSetFlag(i) == /\ pcBar[i] = "r"
               /\ pcBar' = [pcBar EXCEPT ![i] = "a1"]
               /\ flagBar' = [flagBar EXCEPT ![i] = TRUE]
               /\ UNCHANGED turnBar

PSetTurn(i) == /\ pcBar[i] = "a1"
               /\ pcBar' = [pcBar EXCEPT ![i] = "a2"]
               /\ turnBar' = Not(i)
               /\ UNCHANGED flagBar

PEnter(i) == /\ pcBar[i] = "a2"
             /\ (~flagBar[Not(i)] \/ turnBar = i)
             /\ pcBar' = [pcBar EXCEPT ![i] = "cs"]
             /\ UNCHANGED <<flagBar, turnBar>>

PExit(i) == /\ pcBar[i] = "cs"
            /\ pcBar' = [pcBar EXCEPT ![i] = "r"]
            /\ flagBar' = [flagBar EXCEPT ![i] = FALSE]
            /\ UNCHANGED turnBar

PProc(i) == PSetFlag(i) \/ PSetTurn(i) \/ PEnter(i) \/ PExit(i)

PNext == \E i \in Procs : PProc(i)

PFairness == \A i \in Procs : /\ WF_PVars(PSetTurn(i))
                              /\ WF_PVars(PEnter(i))
                              /\ WF_PVars(PExit(i))

PetersonSpec == PInit /\ [][PNext]_PVars /\ PFairness

PMutualExclusion == ~(pcBar[0] = "cs" /\ pcBar[1] = "cs")

PStarvationFree == \A i \in Procs : (pcBar[i] = "a1") ~> (pcBar[i] = "cs")

---------------------------------------------------------------------------
(***************************************************************************)
(* Theorems. LockHS implements Lock, since the auxiliary variables do not *)
(* constrain pc. Under the refinement mapping, LockHS also implements     *)
(* Peterson.                                                               *)
(***************************************************************************)
THEOREM Spec => []Inv
THEOREM Spec => LockSpec
THEOREM Spec => PetersonSpec
THEOREM Spec => []PMutualExclusion
THEOREM Spec => PStarvationFree
THEOREM Spec => StarvationFree
=============================================================================