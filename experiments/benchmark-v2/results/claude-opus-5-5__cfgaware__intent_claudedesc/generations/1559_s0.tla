------------------------------- MODULE LockHS -------------------------------
EXTENDS Naturals

(***************************************************************************)
(* Two processes, 0 and 1.                                                 *)
(***************************************************************************)
Procs == {0, 1}
Other(p) == 1 - p
NoProc == 2

VARIABLES pc, lock, turn, s

lockVars == <<pc, lock>>
varsHS   == <<pc, lock, turn, s>>

(***************************************************************************)
(* The base two-process lock.                                              *)
(*   "a0" : noncritical section                                            *)
(*   "a1" : trying to enter (acquire lock atomically)                      *)
(*   "cs" : critical section                                               *)
(*   "a4" : exiting (release lock)                                         *)
(***************************************************************************)
Init == /\ pc = [p \in Procs |-> "a0"]
        /\ lock = NoProc

NonCrit(p) == /\ pc[p] = "a0"
              /\ pc' = [pc EXCEPT ![p] = "a1"]
              /\ UNCHANGED lock

Enter(p) == /\ pc[p] = "a1"
            /\ lock = NoProc
            /\ lock' = p
            /\ pc' = [pc EXCEPT ![p] = "cs"]

Crit(p) == /\ pc[p] = "cs"
           /\ pc' = [pc EXCEPT ![p] = "a4"]
           /\ UNCHANGED lock

Exit(p) == /\ pc[p] = "a4"
           /\ lock' = NoProc
           /\ pc' = [pc EXCEPT ![p] = "a0"]

Next == \E p \in Procs : NonCrit(p) \/ Enter(p) \/ Crit(p) \/ Exit(p)

Spec == Init /\ [][Next]_lockVars

LockInv ==
  /\ \A p, q \in Procs :
        (pc[p] \in {"cs", "a4"} /\ pc[q] \in {"cs", "a4"}) => p = q
  /\ \A p \in Procs : (pc[p] \in {"cs", "a4"}) <=> (lock = p)

(***************************************************************************)
(* Auxiliary variables.                                                    *)
(*   turn : history variable recording which process was last given the   *)
(*          turn during entry.                                             *)
(*   s    : stuttering variable (Lamport style) expanding the Enter step   *)
(*          into three sub-steps: two added stuttering steps followed by   *)
(*          the real Enter step.                                           *)
(***************************************************************************)
top == [id |-> NoProc, val |-> 0]

InitHS == /\ Init
          /\ turn = 0
          /\ s = top

EnterHS(p) ==
  \/ /\ s = top
     /\ pc[p] = "a1"
     /\ lock = NoProc
     /\ s' = [id |-> p, val |-> 2]
     /\ UNCHANGED <<pc, lock, turn>>
  \/ /\ s = [id |-> p, val |-> 2]
     /\ s' = [id |-> p, val |-> 1]
     /\ turn' = Other(p)
     /\ UNCHANGED <<pc, lock>>
  \/ /\ s = [id |-> p, val |-> 1]
     /\ Enter(p)
     /\ s' = top
     /\ UNCHANGED turn

NextHS ==
  \E p \in Procs :
     \/ s = top /\ NonCrit(p) /\ UNCHANGED <<turn, s>>
     \/ EnterHS(p)
     \/ s = top /\ Crit(p)    /\ UNCHANGED <<turn, s>>
     \/ s = top /\ Exit(p)    /\ UNCHANGED <<turn, s>>

SpecHS == InitHS /\ [][NextHS]_varsHS

TypeOKHS ==
  /\ pc \in [Procs -> {"a0", "a1", "cs", "a4"}]
  /\ lock \in Procs \cup {NoProc}
  /\ turn \in Procs
  /\ s \in {top} \cup [id : Procs, val : {1, 2}]

InvHS ==
  /\ (s # top) => (pc[s.id] = "a1" /\ lock = NoProc)
  /\ (s # top /\ s.val = 1) => (turn = Other(s.id))
  /\ \A p \in Procs : (pc[p] \in {"cs", "a4"}) => (turn = Other(p) /\ lock = p)

(***************************************************************************)
(* Refinement mapping to Peterson's algorithm.                             *)
(***************************************************************************)
ppc == [p \in Procs |->
          IF pc[p] = "a1" /\ s # top /\ s.id = p
            THEN IF s.val = 2 THEN "a2" ELSE "a3"
            ELSE pc[p]]

pflag == [p \in Procs |-> ppc[p] \in {"a2", "a3", "cs", "a4"}]

pturn == turn

pvars == <<ppc, pflag, pturn>>

PInit == /\ ppc = [p \in Procs |-> "a0"]
         /\ pflag = [p \in Procs |-> FALSE]
         /\ pturn = 0

PA0(p) == /\ ppc[p] = "a0"
          /\ ppc' = [ppc EXCEPT ![p] = "a1"]
          /\ UNCHANGED <<pflag, pturn>>

PA1(p) == /\ ppc[p] = "a1"
          /\ pflag' = [pflag EXCEPT ![p] = TRUE]
          /\ ppc' = [ppc EXCEPT ![p] = "a2"]
          /\ UNCHANGED pturn

PA2(p) == /\ ppc[p] = "a2"
          /\ pturn' = Other(p)
          /\ ppc' = [ppc EXCEPT ![p] = "a3"]
          /\ UNCHANGED pflag

PA3(p) == /\ ppc[p] = "a3"
          /\ (pflag[Other(p)] = FALSE \/ pturn = p)
          /\ ppc' = [ppc EXCEPT ![p] = "cs"]
          /\ UNCHANGED <<pflag, pturn>>

PCS(p) == /\ ppc[p] = "cs"
          /\ ppc' = [ppc EXCEPT ![p] = "a4"]
          /\ UNCHANGED <<pflag, pturn>>

PA4(p) == /\ ppc[p] = "a4"
          /\ pflag' = [pflag EXCEPT ![p] = FALSE]
          /\ ppc' = [ppc EXCEPT ![p] = "a0"]
          /\ UNCHANGED pturn

PNext == \E p \in Procs :
           PA0(p) \/ PA1(p) \/ PA2(p) \/ PA3(p) \/ PCS(p) \/ PA4(p)

PSpec == PInit /\ [][PNext]_pvars

THEOREM SpecHS => [](TypeOKHS /\ InvHS /\ LockInv)
THEOREM SpecHS => Spec
THEOREM SpecHS => PSpec
=============================================================================