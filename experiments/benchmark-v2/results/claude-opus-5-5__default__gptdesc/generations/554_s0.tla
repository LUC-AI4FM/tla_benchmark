------------------------------ MODULE Peterson ------------------------------
EXTENDS Integers, TLC

CONSTANT N

ASSUME NPositive == N \in Nat \ {0}

Procs == 0..(N-1)

(***************************************************************************
--algorithm Peterson {
  variables level = [p \in Procs |-> -1],
            last_to_enter = [l \in 0..(N-2) |-> 0];

  fair process (p \in Procs)
    variable lev = 0;
  {
    ncs:- while (TRUE) {
            lev := 0;
      e0:   while (lev < N - 1) {
      e1:     level[self] := lev;
      e2:     last_to_enter[lev] := self;
      e3:     await (last_to_enter[lev] # self)
                    \/ (\A k \in Procs \ {self} : level[k] < lev);
              lev := lev + 1;
            };
      cs:   skip;
      exit: level[self] := -1;
          }
  }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES level, last_to_enter, pc, lev

vars == << level, last_to_enter, pc, lev >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ level = [q \in Procs |-> -1]
        /\ last_to_enter = [l \in 0..(N-2) |-> 0]
        (* Process p *)
        /\ lev = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ lev' = [lev EXCEPT ![self] = 0]
             /\ pc' = [pc EXCEPT ![self] = "e0"]
             /\ UNCHANGED << level, last_to_enter >>

e0(self) == /\ pc[self] = "e0"
            /\ IF lev[self] < N - 1
                  THEN /\ pc' = [pc EXCEPT ![self] = "e1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << level, last_to_enter, lev >>

e1(self) == /\ pc[self] = "e1"
            /\ level' = [level EXCEPT ![self] = lev[self]]
            /\ pc' = [pc EXCEPT ![self] = "e2"]
            /\ UNCHANGED << last_to_enter, lev >>

e2(self) == /\ pc[self] = "e2"
            /\ last_to_enter' = [last_to_enter EXCEPT ![lev[self]] = self]
            /\ pc' = [pc EXCEPT ![self] = "e3"]
            /\ UNCHANGED << level, lev >>

e3(self) == /\ pc[self] = "e3"
            /\ \/ last_to_enter[lev[self]] # self
               \/ \A k \in Procs \ {self} : level[k] < lev[self]
            /\ lev' = [lev EXCEPT ![self] = lev[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "e0"]
            /\ UNCHANGED << level, last_to_enter >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << level, last_to_enter, lev >>

exit(self) == /\ pc[self] = "exit"
              /\ level' = [level EXCEPT ![self] = -1]
              /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ UNCHANGED << last_to_enter, lev >>

p(self) == ncs(self) \/ e0(self) \/ e1(self) \/ e2(self) \/ e3(self)
              \/ cs(self) \/ exit(self)

Next == (\E self \in Procs : p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ p(self))

\* END TRANSLATION

-----------------------------------------------------------------------------
(* Properties *)

TypeOK ==
  /\ level \in [Procs -> -1..(N-2)]
  /\ last_to_enter \in [0..(N-2) -> Procs]
  /\ lev \in [Procs -> 0..(N-1)]
  /\ pc \in [Procs -> {"ncs", "e0", "e1", "e2", "e3", "cs", "exit"}]

MutualExclusion ==
  \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Trying(i) == pc[i] \in {"e0", "e1", "e2", "e3"}

DeadlockFreedom ==
  (\E i \in Procs : Trying(i)) ~> (\E j \in Procs : pc[j] = "cs")

StarvationFreedom ==
  \A i \in Procs : Trying(i) ~> (pc[i] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => StarvationFreedom
=============================================================================