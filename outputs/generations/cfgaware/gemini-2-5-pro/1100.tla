---- MODULE TwoProcessMutex ----
EXTENDS TLC, Integers

CONSTANT Procs
ASSUME Procs = {1, 2}

(*--fair algorithm TwoProcessMutex
variables
  pc = [p \in Procs |-> "ncs"];
  lock = "free";

fair process (p \in Procs)
{
  while (TRUE) {
    ncs:
      skip;
    l1:
      await lock = "free";
      lock := "taken";
    cs:
      lock := "free";
  }
}
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES pc, lock

vars == << pc, lock >>

ProcSet == Procs

Init == (* Global variables *)
        /\ pc = [p \in ProcSet |-> "ncs"]
        /\ lock = "free"

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "l1"]
             /\ UNCHANGED lock

l1(self) == /\ pc[self] = "l1"
            /\ lock = "free"
            /\ lock' = "taken"
            /\ pc' = [pc EXCEPT ![self] = "cs"]

cs(self) == /\ pc[self] = "cs"
            /\ lock' = "free"
            /\ pc' = [pc EXCEPT ![self] = "ncs"]

Next == (\E self \in ProcSet: ncs(self) \/ l1(self) \/ cs(self))

Spec == Init /\ [][Next]_vars

P(self) == ncs(self) \/ l1(self) \/ cs(self)
fairness == \A self \in ProcSet: WF_vars(P(self))

\* END TRANSLATION

TypeOK == /\ pc \in [Procs -> {"ncs", "l1", "cs"}]
          /\ lock \in {"free", "taken"}

LockInv == Cardinality({p \in Procs : pc[p] = "cs"}) <= 1

Liveness == (pc[1] = "l1") ~> (pc[1] = "cs")

THEOREM Spec /\ fairness => Liveness

=============================================================================