----------------------------- MODULE FastMutexTwoGroups -----------------------------
EXTENDS Naturals

CONSTANTS N, M

ASSUME /\ N \in Nat /\ N >= 1
       /\ M \in Nat /\ 1 <= M /\ M <= N

Null == 0
Proc == 1..N
G1 == 1..M
G2 == (M+1)..N

PCStates == {"Try", "CheckY", "WaitY0a", "CheckX", "WaitAllDown", "WaitY0b", "CS"}

VARIABLES flag, X, Y, pc

vars == << flag, X, Y, pc >>

TypeOK ==
  /\ flag \in [Proc -> BOOLEAN]
  /\ X \in Proc \cup {Null}
  /\ Y \in Proc \cup {Null}
  /\ pc \in [Proc -> PCStates]

Init ==
  /\ flag = [p \in Proc |-> FALSE]
  /\ X = Null
  /\ Y = Null
  /\ pc = [p \in Proc |-> "Try"]

OthersDown(p) == \A j \in Proc: j # p => flag[j] = FALSE

(*
  Lamport's fast mutual exclusion algorithm, per-process actions.
  The two groups G1 and G2 execute identical logic but are exposed as
  syntactically distinct process actions to mirror two PlusCal process
  declarations.
*)

A1(p) == /\ pc[p] = "Try"
         /\ flag' = [flag EXCEPT ![p] = TRUE]
         /\ X' = p
         /\ pc' = [pc EXCEPT ![p] = "CheckY"]
         /\ UNCHANGED Y

A2a(p) == /\ pc[p] = "CheckY"
          /\ Y # Null
          /\ flag' = [flag EXCEPT ![p] = FALSE]
          /\ pc' = [pc EXCEPT ![p] = "WaitY0a"]
          /\ UNCHANGED << X, Y >>

A2b(p) == /\ pc[p] = "CheckY"
          /\ Y = Null
          /\ Y' = p
          /\ pc' = [pc EXCEPT ![p] = "CheckX"]
          /\ UNCHANGED << flag, X >>

A3(p) == /\ pc[p] = "WaitY0a"
         /\ Y = Null
         /\ pc' = [pc EXCEPT ![p] = "Try"]
         /\ UNCHANGED << flag, X, Y >>

A4a(p) == /\ pc[p] = "CheckX"
          /\ X = p
          /\ pc' = [pc EXCEPT ![p] = "CS"]
          /\ UNCHANGED << flag, X, Y >>

A4b(p) == /\ pc[p] = "CheckX"
          /\ X # p
          /\ flag' = [flag EXCEPT ![p] = FALSE]
          /\ pc' = [pc EXCEPT ![p] = "WaitAllDown"]
          /\ UNCHANGED << X, Y >>

A5a(p) == /\ pc[p] = "WaitAllDown"
          /\ OthersDown(p)
          /\ Y = p
          /\ Y' = Null
          /\ pc' = [pc EXCEPT ![p] = "WaitY0b"]
          /\ UNCHANGED << flag, X >>

A5b(p) == /\ pc[p] = "WaitAllDown"
          /\ OthersDown(p)
          /\ Y # p
          /\ pc' = [pc EXCEPT ![p] = "Try"]
          /\ UNCHANGED << flag, X, Y >>

A6(p) == /\ pc[p] = "WaitY0b"
         /\ Y = Null
         /\ pc' = [pc EXCEPT ![p] = "Try"]
         /\ UNCHANGED << flag, X, Y >>

A7(p) == /\ pc[p] = "CS"
         /\ Y' = Null
         /\ flag' = [flag EXCEPT ![p] = FALSE]
         /\ pc' = [pc EXCEPT ![p] = "Try"]
         /\ UNCHANGED X

ProcStep(p) ==
  A1(p) \/ A2a(p) \/ A2b(p) \/ A3(p) \/
  A4a(p) \/ A4b(p) \/
  A5a(p) \/ A5b(p) \/
  A6(p) \/ A7(p)

Group1Proc(p) == /\ p \in G1 /\ ProcStep(p)
Group2Proc(p) == /\ p \in G2 /\ ProcStep(p)

Next ==
  ( \E p \in G1: Group1Proc(p) )
  \/ ( \E q \in G2: Group2Proc(q) )

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ (\A p \in G1: WF_vars(Group1Proc(p)))
  /\ (\A q \in G2: WF_vars(Group2Proc(q)))

MutualExclusion ==
  \A p \in Proc: \A q \in Proc:
    p # q => ~(pc[p] = "CS" /\ pc[q] = "CS")

EventuallySomeCS ==
  []<>(\E p \in Proc: pc[p] = "CS")
=============================================================================