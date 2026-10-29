------------------------------ MODULE AbstractLock ------------------------------
(***************************************************************************)
(* An abstract mutual-exclusion lock for two processes.  Each process      *)
(* cycles through a non-critical location "ncs", a waiting location "l1"   *)
(* where it acquires the lock once it is free, the critical section "cs",  *)
(* and then releases the lock.                                             *)
(***************************************************************************)
EXTENDS Naturals, TLC

(***************************************************************************
--algorithm AbstractLock {
    variable lock = TRUE;   \* TRUE means the lock is free

    fair+ process (P \in {1, 2})
    {
      ncs: while (TRUE) {
             skip;
      l1:    await lock;
             lock := FALSE;
      cs:    skip;
             lock := TRUE
           }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES lock, pc

vars == << lock, pc >>

ProcSet == {1, 2}

Init == (* Global variables *)
        /\ lock = TRUE
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "l1"]
             /\ lock' = lock

l1(self) == /\ pc[self] = "l1"
            /\ lock
            /\ lock' = FALSE
            /\ pc' = [pc EXCEPT ![self] = "cs"]

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ lock' = TRUE
            /\ pc' = [pc EXCEPT ![self] = "ncs"]

P(self) == ncs(self) \/ l1(self) \/ cs(self)

Next == (\E self \in {1, 2} : P(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {1, 2} : SF_vars(P(self))

\* END TRANSLATION

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK == /\ lock \in BOOLEAN
          /\ pc \in [ProcSet -> {"ncs", "l1", "cs"}]

MutualExclusion == ~(pc[1] = "cs" /\ pc[2] = "cs")

Liveness == (pc[1] = "l1") ~> (pc[1] = "cs")

=============================================================================