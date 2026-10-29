------------------------------ MODULE Alternate ------------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME NAssump == N \in Nat \ {0}

Procs == 0 .. (N - 1)

(***************************************************************************
--algorithm Alternate {
    variable turn = 0 ;
    fair process (procs \in Procs) {
      ncs:   while (TRUE) {
               skip ;
      enter:   await turn = self ;
      cs:      skip ;
      exit:    turn := (self + 1) % N
             }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES turn, pc

vars == << turn, pc >>

ProcSet == Procs

Init == /\ turn = 0
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "enter"]
             /\ turn' = turn

enter(self) == /\ pc[self] = "enter"
               /\ turn = self
               /\ pc' = [pc EXCEPT ![self] = "cs"]
               /\ turn' = turn

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ turn' = turn

exit(self) == /\ pc[self] = "exit"
              /\ turn' = (self + 1) % N
              /\ pc' = [pc EXCEPT ![self] = "ncs"]

procs(self) == ncs(self) \/ enter(self) \/ cs(self) \/ exit(self)

Next == (\E self \in Procs : procs(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(procs(self))

\* END TRANSLATION

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK == /\ turn \in Procs
          /\ pc \in [Procs -> {"ncs", "enter", "cs", "exit"}]

MutualExclusion == \A p, q \in Procs :
                      (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

\* Only the process holding the turn can be in cs or exit
TurnHolder == \A p \in Procs : pc[p] \in {"cs", "exit"} => turn = p

(* Liveness properties *)

\* Every process waiting to enter eventually reaches the critical section
StarvationFree == \A p \in Procs : (pc[p] = "enter") ~> (pc[p] = "cs")

\* Every process enters its critical section infinitely often
InfinitelyOftenCS == \A p \in Procs : []<>(pc[p] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion /\ TurnHolder)
THEOREM Spec => StarvationFree /\ InfinitelyOftenCS
=============================================================================