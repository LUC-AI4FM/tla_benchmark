---------------------------- MODULE AbstractLock ----------------------------
EXTENDS Naturals, TLC

CONSTANT N
ASSUME N = 2

Procs == 1..N

(***************************************************************************
--algorithm AbstractLock {
    variable lock = 0;   \* 0 means the lock is free, otherwise holder id

    fair+ process (P \in Procs) {
        ncs: while (TRUE) {
                 skip;                        \* non-critical section
        l1:      await lock = 0;              \* wait until lock is free
                 lock := self;                \* acquire
        cs:      skip;                        \* critical section
        l2:      lock := 0                    \* release
             }
    }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES lock, pc

vars == << lock, pc >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ lock = 0
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "l1"]
             /\ lock' = lock

l1(self) == /\ pc[self] = "l1"
            /\ lock = 0
            /\ lock' = self
            /\ pc' = [pc EXCEPT ![self] = "cs"]

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ lock' = lock

l2(self) == /\ pc[self] = "l2"
            /\ lock' = 0
            /\ pc' = [pc EXCEPT ![self] = "ncs"]

P(self) == ncs(self) \/ l1(self) \/ cs(self) \/ l2(self)

Next == (\E self \in Procs: P(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : SF_vars(P(self))

\* END TRANSLATION

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK == /\ lock \in {0} \cup Procs
          /\ pc \in [ProcSet -> {"ncs", "l1", "cs", "l2"}]

MutualExclusion == \A i, j \in Procs :
                      (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

(* Liveness property *)

Liveness == (pc[1] = "l1") ~> (pc[1] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => Liveness
=============================================================================