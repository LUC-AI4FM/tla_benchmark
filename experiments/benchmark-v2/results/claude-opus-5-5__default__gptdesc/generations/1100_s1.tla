---------------------------- MODULE AbstractLock ----------------------------
EXTENDS Naturals

(***************************************************************************
--algorithm AbstractLock {
    variable lock = 0;

    fair+ process (P \in {1, 2})
    {
      ncs: while (TRUE) {
             skip;
      l1:    await lock = 0;
             lock := self;
      cs:    skip;
             lock := 0;
           }
    }
}
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES lock, pc

vars == << lock, pc >>

ProcSet == {1, 2}

Init == /\ lock = 0
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
            /\ lock' = 0
            /\ pc' = [pc EXCEPT ![self] = "ncs"]

P(self) == ncs(self) \/ l1(self) \/ cs(self)

Next == (\E self \in {1, 2} : P(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {1, 2} : SF_vars(P(self))

\* END TRANSLATION

-----------------------------------------------------------------------------

TypeOK == /\ lock \in {0, 1, 2}
          /\ pc \in [ProcSet -> {"ncs", "l1", "cs"}]

MutualExclusion == ~(pc[1] = "cs" /\ pc[2] = "cs")

Liveness == (pc[1] = "l1") ~> (pc[1] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => Liveness

=============================================================================