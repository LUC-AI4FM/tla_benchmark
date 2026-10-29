------------------------------ MODULE SemMutex ------------------------------
EXTENDS Integers

CONSTANT N

ASSUME NPos == N \in Nat /\ N > 0

Procs == 0..(N-1)

(***************************************************************************
--algorithm SemMutex {
  variables sem = 1;
  fair process (p \in Procs) {
    ncs:- while (TRUE) {
            skip;
    enter:+   await sem = 1;
              sem := 0;
    cs:       skip;
    exit:     sem := 1
          }
  }
}
 ***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES sem, pc

vars == << sem, pc >>

ProcSet == Procs

Init == /\ sem = 1
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "enter"]
             /\ sem' = sem

enter(self) == /\ pc[self] = "enter"
               /\ sem = 1
               /\ sem' = 0
               /\ pc' = [pc EXCEPT ![self] = "cs"]

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ sem' = sem

exit(self) == /\ pc[self] = "exit"
              /\ sem' = 1
              /\ pc' = [pc EXCEPT ![self] = "ncs"]

p(self) == ncs(self) \/ enter(self) \/ cs(self) \/ exit(self)

Next == (\E self \in Procs: p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : /\ WF_vars((pc[self] # "ncs") /\ p(self))
                               /\ SF_vars(enter(self))

\* END TRANSLATION

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety and liveness properties                                          *)
(***************************************************************************)

TypeOK == /\ sem \in {0, 1}
          /\ pc \in [Procs -> {"ncs", "enter", "cs", "exit"}]

InCS(i) == pc[i] \in {"cs", "exit"}

MutualExclusion == \A i, j \in Procs : (i # j) => ~(InCS(i) /\ InCS(j))

SemInv == (sem = 1) <=> (\A i \in Procs : ~InCS(i))

Inv == TypeOK /\ MutualExclusion /\ SemInv

StarvationFree == \A i \in Procs : (pc[i] = "enter") ~> (pc[i] = "cs")

DeadlockFree == (\E i \in Procs : pc[i] = "enter") ~> (\E i \in Procs : pc[i] = "cs")

THEOREM Spec => []Inv
THEOREM Spec => StarvationFree
THEOREM Spec => DeadlockFree
=============================================================================