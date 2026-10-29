---------------------------- MODULE LockHSPeterson ----------------------------
EXTENDS Integers

Proc == {0, 1}

Other(p) == 1 - p

VARIABLES pc, h, s

lockVars == <<pc>>
vars == <<pc, h, s>>

NoStutter == [ctx |-> -1, cnt |-> 0]

-----------------------------------------------------------------------------
(* High-level two-process lock                                              *)
-----------------------------------------------------------------------------

LockInit == pc = [p \in Proc |-> "ncs"]

Enter(p) == /\ pc[p] = "ncs"
            /\ pc[Other(p)] # "cs"
            /\ pc' = [pc EXCEPT ![p] = "cs"]

Exit(p) == /\ pc[p] = "cs"
           /\ pc' = [pc EXCEPT ![p] = "ncs"]

LockNext == \E p \in Proc : Enter(p) \/ Exit(p)

Spec == LockInit /\ [][LockNext]_lockVars

LockTypeOK == pc \in [Proc -> {"ncs", "cs"}]

LockInv == ~(pc[0] = "cs" /\ pc[1] = "cs")

-----------------------------------------------------------------------------
(* Lock with history variable h (records turn at the moment it is assigned) *)
(* and stuttering variable s (encodes the extra internal entry micro-steps). *)
(*   s.ctx : process performing the stutters (-1 if none)                  *)
(*   s.cnt : number of remaining internal stutter steps                     *)
-----------------------------------------------------------------------------

InitHS == /\ LockInit
          /\ h = 0
          /\ s = NoStutter

EnterHS(p) == /\ s = NoStutter
              /\ Enter(p)
              /\ s' = [ctx |-> p, cnt |-> 2]
              /\ UNCHANGED h

(* First internal micro-step: assignment of turn, recorded in history h *)
StutTurn(p) == /\ s.ctx = p
               /\ s.cnt = 2
               /\ s' = [ctx |-> p, cnt |-> 1]
               /\ h' = Other(p)
               /\ UNCHANGED pc

(* Second internal micro-step: the wait test succeeds *)
StutWait(p) == /\ s.ctx = p
               /\ s.cnt = 1
               /\ s' = NoStutter
               /\ UNCHANGED <<pc, h>>

ExitHS(p) == /\ s = NoStutter
             /\ Exit(p)
             /\ UNCHANGED <<h, s>>

NextHS == \E p \in Proc :
            EnterHS(p) \/ StutTurn(p) \/ StutWait(p) \/ ExitHS(p)

SpecHS == InitHS /\ [][NextHS]_vars

TypeOKHS == /\ LockTypeOK
            /\ h \in Proc
            /\ s \in [ctx : Proc \cup {-1}, cnt : 0..2]
            /\ (s.ctx = -1) <=> (s.cnt = 0)

InvHS == /\ LockInv
         /\ \A p \in Proc :
              (pc[p] = "cs" /\ s # NoStutter) =>
                 /\ s.ctx = p
                 /\ (s.cnt = 1 => h = Other(p))
         /\ s # NoStutter => pc[s.ctx] = "cs"

-----------------------------------------------------------------------------
(* Refinement mapping to Peterson's algorithm                               *)
-----------------------------------------------------------------------------

pcBar == [p \in Proc |->
            IF pc[p] = "ncs" THEN "a1"
            ELSE IF s.ctx = p /\ s.cnt = 2 THEN "a2"
            ELSE IF s.ctx = p /\ s.cnt = 1 THEN "a3"
            ELSE "cs"]

flagBar == [p \in Proc |-> pcBar[p] # "a1"]

turnBar == h

pVars == <<pcBar, turnBar>>

PInit == /\ pcBar = [p \in Proc |-> "a1"]
         /\ turnBar \in Proc

PA1(p) == /\ pcBar[p] = "a1"
          /\ pcBar' = [pcBar EXCEPT ![p] = "a2"]
          /\ turnBar' = turnBar

PA2(p) == /\ pcBar[p] = "a2"
          /\ pcBar' = [pcBar EXCEPT ![p] = "a3"]
          /\ turnBar' = Other(p)

PA3(p) == /\ pcBar[p] = "a3"
          /\ (~flagBar[Other(p)] \/ turnBar = p)
          /\ pcBar' = [pcBar EXCEPT ![p] = "cs"]
          /\ turnBar' = turnBar

PCS(p) == /\ pcBar[p] = "cs"
          /\ pcBar' = [pcBar EXCEPT ![p] = "a1"]
          /\ turnBar' = turnBar

PNext == \E p \in Proc : PA1(p) \/ PA2(p) \/ PA3(p) \/ PCS(p)

PSpec == PInit /\ [][PNext]_pVars

PMutex == ~(pcBar[0] = "cs" /\ pcBar[1] = "cs")

-----------------------------------------------------------------------------
THEOREM SpecHS => []TypeOKHS
THEOREM SpecHS => []InvHS
THEOREM Spec => []LockInv
THEOREM SpecHS => Spec
THEOREM SpecHS => PSpec
=============================================================================