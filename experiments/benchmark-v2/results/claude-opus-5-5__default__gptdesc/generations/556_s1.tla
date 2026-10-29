---- MODULE SemMutex ----
EXTENDS Integers, Naturals, TLC

CONSTANT N

ASSUME N \in Nat \ {0}

Procs == 0..(N-1)

(* --algorithm SemMutex
variables sem = 1;
process (p \in Procs)
begin
ncs:   while TRUE do
          skip;
enter:    await sem = 1;
          sem := 0;
cs:       skip;
exit:     sem := 1;
       end while;
end process
end algorithm *)

\* BEGIN TRANSLATION
VARIABLES sem, pc

vars == << sem, pc >>

ProcSet == (Procs)

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

TypeOK == /\ sem \in {0, 1}
          /\ pc \in [Procs -> {"ncs", "enter", "cs", "exit"}]

InCS(i) == pc[i] \in {"cs", "exit"}

MutualExclusion == \A i, j \in Procs : (i # j) => ~(InCS(i) /\ InCS(j))

SemConsistent == (sem = 0) <=> (\E i \in Procs : InCS(i))

StarvationFree == \A i \in Procs : (pc[i] = "enter") ~> (pc[i] = "cs")

DeadlockFree == (\E i \in Procs : pc[i] = "enter") ~> (\E i \in Procs : pc[i] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion /\ SemConsistent)
THEOREM Spec => StarvationFree
====